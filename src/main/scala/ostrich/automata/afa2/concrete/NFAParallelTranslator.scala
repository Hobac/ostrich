/**
 * This file is part of Ostrich, an SMT solver for strings.
 * Copyright (c) 2022-2023 Philipp Ruemmer. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ostrich.automata.afa2.concrete

import ap.util.Combinatorics
import ostrich.automata.afa2.StepTransition
import ostrich.automata.afa2.symbolic.SymbEpsReducer
import ostrich.automata.{AutomataUtils, BricsAutomaton, BricsAutomatonBuilder}

import java.util.concurrent.atomic.{AtomicBoolean, AtomicInteger}
import java.util.concurrent.{ConcurrentHashMap, ConcurrentLinkedQueue, Executors, LinkedBlockingQueue, TimeUnit}
import scala.collection.mutable.{MultiMap, HashMap => MHashMap, HashSet => MHashSet, Set => MSet}

object NFATranslatorParallel {
  def apply(afa: AFA2): BricsAutomaton =
    new ParallelNFATranslator(afa).result
}


class ParallelNFATranslator(afa : AFA2) {

  import afa._
  import ostrich.automata.afa2.{Left, Right, Step}

  // union of categorised states
  private val categorisedStates =
    irStates ++ llStates ++ lrStates ++ rlStates ++ rrStates ++ rfStates

  // state set and union of categorized state sets must be the same
  assert(states.toSet == categorisedStates &&
    states.size == irStates.size + llStates.size + lrStates.size +
      rlStates.size + rrStates.size + rfStates.size,
    "2AFA states cannot be classified into ir, ll, lr, rl, rr, rf. " +
      "Problem states: " +
      (states filterNot categorisedStates).mkString(", "))

  // only one inital state
  assert(irStates.size == 1)

  assert(transitions forall {
    case (_, ts) => ts forall {
      case StepTransition(_, _, targets) => targets.nonEmpty
    }},
    "Transitions with zero target states are not supported")

  // TODO: check that automaton is not looping
  // (requires Parikh image computation)

  private val activeWorkers = new AtomicInteger(0)
  private val maxActiveWorkers = new AtomicInteger(0)

  type MacroState = Set[Int]
  case class Edge(from: MacroState,  label: Int, to: MacroState)
  case class EpsilonEdge(from: MacroState, to: MacroState)

  // states that leave by moving right
  private val xrStates = irStates ++ rrStates ++ lrStates

  // states that leave by moving left
  private val xlStates = llStates ++ rlStates

  // states that were entered by moving right
  private val rxStates = rfStates ++ rrStates ++ rlStates

  // states that were entered by moving left
  private val lxStates = llStates ++ lrStates

  // get all transitions from state that read the given label
  def outgoing(state: Int, label: Int): Seq[(Step, Seq[Int])] = {
    transitions.getOrElse(state, List())
      .filter(_.label == label)
      .map(t => (t.step, t.targets))
  }

  // check if there is a left-moving transition whose targets satisfy the condition
  def existsGoingLeft(transitions: Seq[(Step, Seq[Int])], condition: Seq[Int] => Boolean): Boolean =
    transitions.exists(t => t._1 == Left && condition(t._2))

  // check if there is a right-moving transition whose targets satisfy the condition
  def existsGoingRight(transitions: Seq[(Step, Seq[Int])], condition: Seq[Int] => Boolean): Boolean =
    transitions.exists(t => t._1 == Right && condition(t._2))

  // Condition 3: (no sink states in Q)
  // Final-right and right-left states cannot occur in the source macro-state
  def possibleFromState(state : Int) : Boolean = {
    (!(rfStates contains state)) && (!(rlStates contains state))
  }

  /** Checks whether a state can be part of Q while satisfying conditions 3, 5, and 7. */
  def possibleFromState(state : Int, label : Int, toStates : Set[Int]) : Boolean = {
    // Condition 3: (no sink states in Q)
    possibleFromState(state) && (
      // Condition 5: Right-successors.
      // Every xr state (left from left to right) in Q must have a right transition whose
      // existential target is in Q' or whose universal targets are all in Q'.
      !(xrStates contains state) || outgoing(state, label).exists(t => t._1 == Right && t._2.forall(toStates.contains))
      ) && (
      // Condition 7: every lx state in Q (entered from right to left)
      // must have a matching left-moving transition from some state in Q' back to it
      !(lxStates contains state) || toStates.exists(toState =>
        outgoing(toState, label).exists(t => t._1 == Left && t._2.contains(state)))
      )
  }

  /**
   * Precomputes the requirements that a state in Q imposes on Q'.
   *
   * For each (state, label), the result contains requirements of the form:
   * Seq(Set(...), Set(...)), meaning that Q' must contain at least one of these sets.
   *
   * Example:
   * Seq(Set(4), Set(7, 8)) means Q' must contain 4 OR both 7 and 8.
   *
   * xr states create a Condition 5 requirement:
   * Q' must contain all targets of at least one right-moving transition from that state.
   *
   * lx states create a Condition 7 requirement:
   * Q' must contain at least one state with a left-moving transition back to that state.
   */
  val fromStateImplications : Map[(Int /* state */, Int /* label */),
    Seq[Seq[Set[Int]]]] =
    (for (label <- letters.iterator; state <- states.iterator) yield {
      (state, label) -> {

        // Condition 5: for an xr state, collect the possible target sets of
        // its right-moving transitions. Q' must contain one of these sets.
        (if (xrStates contains state)
          List(minElements(for ((Right, targets) <- outgoing(state, label))
            yield targets))
        else
          List()) ++
          // Condition 7: for an lx state, collect all states that have a
          // left-moving transition back to it. Q' must contain one of them.
          (if (lxStates contains state)
            List(for (toState <- states.toList;
                      if existsGoingLeft(outgoing(toState, label),
                        targets => targets contains state))
            yield Set(toState))
          else
            List())
      }
    }).toMap

  def minElements(sets : Seq[Seq[Int]]) : Seq[Set[Int]] = {
    var imps : List[Set[Int]] = List()
    def addImp(s : Set[Int]) : Unit =
      if (!(imps exists {t => t subsetOf s})) {
        imps = imps filterNot { t => s subsetOf t }
        imps = s :: imps
      }

    for (s <- sets)
      addImp(s.toSet)

    imps
  }

  // Condition 4: no source states in Q'
  def possibleToState(state : Int) : Boolean = {
    (!(irStates contains state)) && (!(lrStates contains state))
  }

  /** Checks whether a state can be part of Q' while satisfying conditions 4, 6, and 8. */
  def possibleToState(state : Int, label : Int, fromStates : Set[Int]) : Boolean = {
    // Condition 4: no source states in Q'
    possibleToState(state) && (
      // Condition 6: every xl state in Q' (leaves by moving left)
      // must have a left-moving transition whose targets are contained in Q
      !(xlStates contains state) ||
        outgoing(state, label).exists(t => t._1 == Left && t._2.forall(fromStates.contains))
      ) && (
      // Condition 8: every rx state in Q' (entered from left to right)
      // must have a matching right-moving transition from some state in Q to this state
      !(rxStates contains state) || fromStates.exists(fromState =>
          outgoing(fromState, label).exists(t => t._1 == Right && t._2.contains(state)))
      )
  }

  private val edges = new ConcurrentLinkedQueue[Edge]()
  private val epsilonEdges = new ConcurrentLinkedQueue[EpsilonEdge]()
  private val discovered = ConcurrentHashMap.newKeySet[Set[Int]]()
  private val workQueue = new LinkedBlockingQueue[Set[Int]]()
  private val pendingStates = new AtomicInteger(0)

  // initial state is {init}
  private val initialMacroStates = irStates.map(s => Set(s))
  for (state <- initialMacroStates)
    schedule(state)

  // schedules the successor states that are reachable via epsilon transitions
  // defined by Condition 1 and 2
  def addEPSReachableStates(state: MacroState): Unit = {
    // lr states can be added anytime
    for (lrState <- lrStates.iterator;
         if !(state contains lrState)) {

      val target = state + lrState
      epsilonEdges.add(EpsilonEdge(state, target))
      schedule(target)
    }

    // rl states can be removed anytime
    for (rlState <- rlStates.iterator;
         if (state contains rlState)) {

      val target = state - rlState
      epsilonEdges.add(EpsilonEdge(state, target))
      schedule(target)
    }
  }

  // Computes the possible Q' states that can support each lx state in Q.
  // A state can support an lx state if it has a left-moving transition
  // that contains the lx state and whose targets are all contained in Q.
  def leftPredecessorChoices(fromStates: MacroState, label: Int): Seq[Seq[Set[Int]]] = {
    for {
      state <- fromStates.toSeq
      if lxStates contains state
    } yield {
      for {
        toState <- states
        if existsGoingLeft(
          outgoing(toState, label),
          targets =>
            (targets contains state) &&
              (targets forall fromStates)
        )
      } yield Set(toState)
    }
  }

  // Computes the possible right-successor sets that support a state in Q'.
  // The state must occur in the target set of a right-moving transition from Q.
  // The complete target set is returned because all targets must be contained in Q'.
  def rightSuccessorChoices(state: Int, fromStates: MacroState, label: Int): Seq[Set[Int]] = {
    if (!(rxStates contains state))
      return Seq(Set.empty)

    for {
      fromState <- fromStates.toSeq
      (Right, targets) <- outgoing(fromState, label)
      if targets contains state
    } yield targets.toSet
  }

  def addLabelReachableStates(fromStates: MacroState): Unit = {
    // Builds all possible lower bounds for Q' that satisfy the given requirements
    // Each requirement contains alternative sets, of which at least one must be contained in Q'
    def lowerBounds(cur : Set[Int], imps : List[Seq[Set[Int]]]) : Iterator[Set[Int]] =
      imps match {
        case List() =>
          Iterator(cur)
        case Seq() :: _ =>
          Iterator.empty
        case imp :: rest if (imp exists { s => s subsetOf cur }) =>
          lowerBounds(cur, rest)
        case imp :: rest =>
          for (s <- imp.iterator; res <- lowerBounds(cur ++ s, rest))
            yield res
      }

    // if there is a state in the fromStates that has no valid successor
    // for example a right final state or a lr turn around state we can stop
    if (fromStates exists { s => !possibleFromState(s) })
      return

    // generate successors independently for every possible input letter
    for (label <- letters) {
      // all Q' macro-states already considered for this Q and label
      val consideredToStates = new MHashSet[Set[Int]]

      // compute the largest possible target macro state
      // any state that fails possibleToState can never occur in a successor
      val upperToBound =
        (for (s <- states.iterator; if possibleToState(s, label, fromStates))
          yield s).toSet

      if (upperToBound.nonEmpty) {

        // Collect all requirements (states) imposed by states in Q
        // Each requirement contains alternative state sets that could satisfy it in Q'
        // Seq(Set(4), Set(7, 8)) means Q' needs 4 OR both 7 and 8.
        // Example: Q = {1, 2}
        // state 1 requires: Seq(Set(4), Set(7, 8)) -> Q' must contain 4 OR both 7 and 8
        // state 2 requires: Seq(Set(5), Set(9)) -> Q' must contain 5 OR 9
        // Possible Q' lower bounds are therefore:
        // {4,5}, {4,9}, {7,8,5}, {7,8,9}
        // Alternatives containing states that are not allowed in Q' are removed.
        val lowerBoundDisjuncts =
          (for (s <- fromStates; imps <- fromStateImplications((s, label)))
            yield imps filter { s =>
              s subsetOf upperToBound }).toList.sortBy(_.size)

        // iterate all lower bounds
        for (lowerToBound <- lowerBounds(Set(), lowerBoundDisjuncts)) {
          // not yet considered
          if (!(consideredToStates contains lowerToBound)) {

            // start with the lower bound already required for Q'
            // the lower bound is not necessarily a valid successor yet
            var targetCandidates = Seq(lowerToBound)

            // Add the required left-predecessor choices for states in Q.
            // Every requirement can branch the current Q' candidates into several new ones.
            for (choices <- leftPredecessorChoices(fromStates, label)) {
              // candidates produced while satisfying this one requirement
              var nextCandidates: Seq[MacroState] = Seq()
              // try to extend every Q' candidate we already have
              // at first this is only the lower bound
              for (candidate <- targetCandidates) {
                // try every possible way of satisfying the current requirement
                for (choice <- choices) {
                  // add the chosen supporting states to the current Q' candidate
                  val newCandidate = candidate ++ choice
                  // only keep the candidate if all of its states are allowed in Q'
                  if (newCandidate subsetOf upperToBound)
                    // remember this as a possible Q' candidate
                    nextCandidates = nextCandidates :+ newCandidate
                }
              }

              // continue with the candidates that satisfy this requirement
              targetCandidates = nextCandidates
            }

            // start with the Q' candidates that already satisfy the previous requirement
            var completedTargetCandidates = targetCandidates

            // becomes true once every current Q' candidate satisfies the remaining support requirements
            var allCandidatesSupported = false

            // repeat until no candidate needs to be extended anymore
            while (!allCandidatesSupported) {
              allCandidatesSupported = true

              // candidates generated in this iteration
              var nextCandidates: Seq[MacroState] = Seq()

              // process every current Q' candidate
              for (candidate <- completedTargetCandidates) {

                // find an rx state in this Q' candidate that is not yet supported
                // by any right-moving transition from Q
                val unsupportedState =
                  candidate.find { state =>
                    (rxStates contains state) &&
                      !rightSuccessorChoices(state, fromStates, label).exists(_ subsetOf candidate)
                  }

                unsupportedState match {
                  case None =>
                    // every rx state in this Q' candidate is already supported
                    nextCandidates = nextCandidates :+ candidate

                  case Some(state) =>
                    // this candidate still needs to be extended
                    allCandidatesSupported = false

                    // try every possible right-successor set that can support this state
                    for (support <- rightSuccessorChoices(state, fromStates, label)) {

                      // add the support states to the current Q' candidate
                      val newCandidate = candidate ++ support

                      // only keep the candidate if all states are still allowed in Q'
                      if (newCandidate subsetOf upperToBound)
                        nextCandidates = nextCandidates :+ newCandidate
                    }
                }
              }

              // use the newly generated candidates in the next iteration
              completedTargetCandidates = nextCandidates
            }

            // schedule the generated successor macro-states
            for (candidate <- completedTargetCandidates) {
              if (consideredToStates add candidate) {
                edges.add(Edge(fromStates, label, candidate))
                schedule(candidate)
              }
            }
          }
        }
      }
    }
  }

  // parallel computation with worker pool
  private def schedule(state: Set[Int]): Unit = {
    if (discovered.add(state)) {
      pendingStates.incrementAndGet()
      workQueue.put(state)
    }
  }

  private val workerCount =
    math.max(1, Runtime.getRuntime.availableProcessors())

  private val executor =
    Executors.newFixedThreadPool(workerCount)

  private val workers =
    for (_ <- 0 until workerCount) yield {
      executor.submit(new Runnable {
        override def run(): Unit = {
          var running = true

          while (running) {
            if (pendingStates.get() == 0) {
              running = false
            } else {
              val state =
                workQueue.poll(50, TimeUnit.MILLISECONDS)

              if (state != null) {
                try {
                  ap.util.Timeout.check

                  val active = activeWorkers.incrementAndGet()
                  var old = maxActiveWorkers.get()
                  while (active > old &&
                    !maxActiveWorkers.compareAndSet(old, active))
                    old = maxActiveWorkers.get()

                  addEPSReachableStates(state)
                  addLabelReachableStates(state)

                } finally {
                  activeWorkers.decrementAndGet()
                  pendingStates.decrementAndGet()
                }
              }
            }
          }
        }
      })
    }

  executor.shutdown()

  for (worker <- workers)
    worker.get()

  // build the bricks automaton
  // 1. Step: Add states and mark inital/final
  val builder = new BricsAutomatonBuilder
  builder.setMinimize(true)

  val setStates = new MHashMap[MacroState, BricsAutomaton#State]

  private val stateIterator = discovered.iterator()
  while (stateIterator.hasNext) {
    val state = stateIterator.next()
    val bricsState = builder.getNewState

    if (state subsetOf rfStates)
      builder.setAccept(bricsState, true)

    setStates.put(state, bricsState)
  }

  for (state <- initialMacroStates)
    builder.setInitialState(setStates(state))

  // 2. Step: Add epsilon edges
  val epsilons =
    new MHashMap[BricsAutomaton#State, MSet[BricsAutomaton#State]]
      with MultiMap[BricsAutomaton#State, BricsAutomaton#State]

  private val epsilonIterator = epsilonEdges.iterator()
  while (epsilonIterator.hasNext) {
    val edge = epsilonIterator.next()

    epsilons.addBinding(
      setStates(edge.from),
      setStates(edge.to)
    )
  }

  // 3. Step: Add sigma transitions
  private val edgeIterator = edges.iterator()
  while (edgeIterator.hasNext) {
    val edge = edgeIterator.next()

    builder.addTransition(
      setStates(edge.from),
      (edge.label.toChar, edge.label.toChar),
      setStates(edge.to)
    )
  }

  AutomataUtils.buildEpsilons(builder, epsilons)
  val result: BricsAutomaton = builder.getAutomaton

  println("Max active workers: " + maxActiveWorkers.get())
  println("Parallel-NFA size: " + result.states.size)
}