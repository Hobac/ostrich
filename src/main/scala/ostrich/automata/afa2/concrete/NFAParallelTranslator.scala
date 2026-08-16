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

import java.util.concurrent.atomic.AtomicInteger
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

  val xrStates = irStates ++ rrStates ++ lrStates
  val xlStates = llStates ++ rlStates
  val rxStates = rfStates ++ rrStates ++ rlStates
  val lxStates = llStates ++ lrStates


  def outgoing(state : Int, l : Int) : Seq[(Step, Seq[Int])] =
    for (StepTransition(`l`, step, ts) <- transitions.getOrElse(state, List())) yield {
      (step, ts)
    }

  def existsGoingLeft(ts : Seq[(Step, Seq[Int])],
                      f : Seq[Int] => Boolean) : Boolean = {
    ts exists {
      case (Left, targets) => f(targets)
      case _                    => false
    }
  }

  def existsGoingRight(ts : Seq[(Step, Seq[Int])],
                       f : Seq[Int] => Boolean) : Boolean = {
    ts exists {
      case (Right, targets) => f(targets)
      case _                     => false
    }
  }

  def possibleFromState(state : Int) : Boolean = {
    (
      !(rfStates contains state)
      ) && (
      !(rlStates contains state)
      )
  }

  def possibleFromState(state    : Int,
                        label    : Int,
                        toStates : Set[Int]) : Boolean = {
    possibleFromState(state) && (
      // ?r states have successors in toStates
      !(xrStates contains state) ||
        existsGoingRight(outgoing(state, label),
          targets => targets forall toStates)
      ) && (
      // l? states have predecessors in toStates
      !(lxStates contains state) ||
        (toStates exists { toState =>
          existsGoingLeft(outgoing(toState, label),
            targets => targets contains state)
        })
      )
  }

  /**
   * If <code>state</code> is contained in a from-state, then one of
   * the given result sets has to be contained in the corresponding
   * to-state.
   */
  val fromStateImplications : Map[(Int /* state */, Int /* label */),
    Seq[Seq[Set[Int]]]] =
    (for (label <- letters.iterator; state <- states.iterator) yield {
      (state, label) -> {
        (if (xrStates contains state)
          List(minElements(for ((Right, targets) <- outgoing(state, label))
            yield targets))
        else
          List()) ++
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

  def possibleToState(state : Int) : Boolean = {
    (
      !(irStates contains state)
      ) && (
      !(lrStates contains state)
      )
  }

  def possibleToState(state      : Int,
                      label      : Int,
                      fromStates : Set[Int]) : Boolean = {
    possibleToState(state) && (
      // ?l states have successors in fromStates
      !(xlStates contains state) ||
        existsGoingLeft(outgoing(state, label),
          targets => targets forall fromStates)
      ) && (
      // r? states have predecessors in fromStates
      !(rxStates contains state) ||
        (fromStates exists { fromState =>
          existsGoingRight(outgoing(fromState, label),
            targets => targets contains state)
        })
      )
  }

  def transitionExists(fromStates : Set[Int],
                       label : Int,
                       toStates : Set[Int]) : Boolean = {
    (

      fromStates forall { state =>

        possibleFromState(state, label, toStates) && (

          // l? states have predecessors in toStates
          !(lxStates contains state) ||
            (toStates exists { toState =>
              existsGoingLeft(outgoing(toState, label),
                targets =>
                  (targets contains state) &&
                    (targets forall fromStates))
            })

          )

      }) && (

      toStates forall { state =>

        possibleToState(state, label, fromStates) && (

          // r? states have predecessors in fromStates
          !(rxStates contains state) ||
            (fromStates exists { fromState =>
              existsGoingRight(outgoing(fromState, label),
                targets =>
                  (targets contains state) &&
                    (targets forall toStates))
            })

          )

      }

      )
  }

  private val edges =
    new ConcurrentLinkedQueue[Edge]()

  private val epsilonEdges =
    new ConcurrentLinkedQueue[EpsilonEdge]()

  private val discovered =
    ConcurrentHashMap.newKeySet[Set[Int]]()

  private val workQueue =
    new LinkedBlockingQueue[Set[Int]]()

  private val pendingStates =
    new AtomicInteger(0)

  // Initial state is {init}
  val initialMacroStates = irStates.map(s => Set(s))
  for (state <- initialMacroStates)
    schedule(state)

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

  def addLabelReachableStates(fromStates: MacroState): Unit = {
    if (fromStates exists { s => !possibleFromState(s) })
      return

    for (label <- letters) {
      val consideredToStates = new MHashSet[Set[Int]]

      def lowerBounds(cur : Set[Int],
                      imps : List[Seq[Set[Int]]]) : Iterator[Set[Int]] =
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

      val upperToBound =
        (for (s <- states.iterator; if (possibleToState(s, label, fromStates)))
          yield s).toSet

      if (!upperToBound.isEmpty) {
        val lowerBoundDisjuncts =
          (for (s <- fromStates; imps <- fromStateImplications((s, label)))
            yield (imps filter { s =>
              s subsetOf upperToBound })).toList.sortBy(_.size)

        for (lowerToBound <- lowerBounds(Set(), lowerBoundDisjuncts)) {
          assert(lowerToBound subsetOf upperToBound)
          if (!(consideredToStates contains lowerToBound)) {

            // TODO: Prevent generating all subsets of the dif between upper and lower bound, enforce conditions 5 and 7 directly!
            val diff = upperToBound -- lowerToBound
            for (s <- Combinatorics.genSubMultisets(diff.toSeq.sorted)) {
              val candidate = lowerToBound ++ s
              if (consideredToStates add candidate) {
                if (transitionExists(fromStates, label, candidate)) {
                  edges.add(Edge(fromStates, label, candidate))
                  schedule(candidate)
                }
              }
            }
          }
        }
      }
    }
  }

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

  // Also propagates exceptions thrown by workers.
  for (worker <- workers)
    worker.get()

  // build the bricks automaton
  // 1. Step: Add states and mark inital/final
  val builder = new BricsAutomatonBuilder
  builder.setMinimize(true)

  val setStates = new MHashMap[MacroState, BricsAutomaton#State]

  val stateIterator = discovered.iterator()
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

  val epsilonIterator = epsilonEdges.iterator()
  while (epsilonIterator.hasNext) {
    val edge = epsilonIterator.next()

    epsilons.addBinding(
      setStates(edge.from),
      setStates(edge.to)
    )
  }

  // 3. Step: Add sigma transitions
  val edgeIterator = edges.iterator()
  while (edgeIterator.hasNext) {
    val edge = edgeIterator.next()

    builder.addTransition(
      setStates(edge.from),
      (edge.label.toChar, edge.label.toChar),
      setStates(edge.to)
    )
  }

  println("Max active workers: " + maxActiveWorkers.get())
  AutomataUtils.buildEpsilons(builder, epsilons)
  val result = builder.getAutomaton
}