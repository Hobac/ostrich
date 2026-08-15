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
import scala.collection.mutable.{MultiMap, HashMap => MHashMap, HashSet => MHashSet, Set => MSet}
import java.util.concurrent.{ConcurrentHashMap, Executors, LinkedBlockingQueue, TimeUnit}
import java.util.concurrent.atomic.AtomicInteger
import ap.util.Combinatorics
import ostrich.automata.afa2.{Left, Right}
import scala.collection.mutable


object NFAParallelTranslator {
  def apply(afa: AFA2): BricsAutomaton =
    new NFAParallelTranslator(afa).result
}


class NFAParallelTranslator(afa : AFA2) {
  type MacroState = Set[Int]
  case class Edge(from: MacroState, label: Int, to: MacroState)
  case class EpsilonEdge(from: MacroState, to: MacroState)

  private val numWorkers = Runtime.getRuntime.availableProcessors()

  // All macro states that have already been discovered.
  private val discovered = ConcurrentHashMap.newKeySet[MacroState]()
  private val edges = ConcurrentHashMap.newKeySet[Edge]()
  private val epsilonEdges = ConcurrentHashMap.newKeySet[EpsilonEdge]()

  // Macro states that still need to be expanded.
  private val workQueue = new LinkedBlockingQueue[MacroState]()

  val xrStates = afa.irStates ++ afa.rrStates ++ afa.lrStates
  val xlStates = afa.llStates ++ afa.rlStates
  val rxStates = afa.rfStates ++ afa.rrStates ++ afa.rlStates
  val lxStates = afa.llStates ++ afa.lrStates

  val stateRoles: Map[Int, String] =
    (afa.irStates.map(_ -> "ir") ++
      afa.rrStates.map(_ -> "rr") ++
      afa.rlStates.map(_ -> "rl") ++
      afa.lrStates.map(_ -> "lr") ++
      afa.llStates.map(_ -> "ll") ++
      afa.rfStates.map(_ -> "rf")).toMap

  val outgoingTransitions: Map[Int, Seq[StepTransition]] =
    afa.transitions

  val incomingTransitions: Map[Int, Seq[(Int, StepTransition)]] =
    afa.incomingTransitions

  /**
   * Add a state to the work queue if it has not been discovered before.
   */
  private def schedule(state: MacroState) = {
    if (discovered.add(state)) {
      workQueue.put(state)
    }
  }

  private def expand(state: MacroState) = {

    // condition 1: lr states can be added
    for (lrState <- afa.lrStates if !state.contains(lrState)) {
      val nextState = state + lrState

      epsilonEdges.add(EpsilonEdge(state, nextState))
      schedule(nextState)
    }

    // condition 2: rl states can be removed
    for (rlState <- afa.rlStates if state.contains(rlState)) {
      val nextState = state - rlState

      epsilonEdges.add(EpsilonEdge(state, nextState))
      schedule(nextState)
    }

    // condition 3, no sinks in Q
    if (state.exists(s => stateRoles(s) != "rf")) {
      // loop symbols and build reached states
      for (label <- afa.letters) {

        def getRightSuccessors(state: MacroState, label: Int): Seq[Int] = {
          state
            .filter(s => Set("ir", "rr", "lr").contains(stateRoles(s)))
            .flatMap(s => outgoingTransitions.getOrElse(s, Seq.empty)
              .filter(_.label == label)
              .flatMap(_.targets))
            .toSeq
        }

        def getRightPredecessors(state: MacroState, label: Int): Seq[Int] = {
          state
            .flatMap(s => incomingTransitions.getOrElse(s, Seq.empty)
              .filter { case (_, transition) =>
                transition.label == label && transition.step == Right
              }
              .map(_._1))
            .toSeq
        }

        // build candidate successor macro state
        // from condition 5 and 7 Q -> Q'
        var nextState: MacroState =
          (getRightSuccessors(state, label) ++ getRightPredecessors(state, label)).toSet

        def satisfiesLeftSuccessors(s: Int): Boolean = {
          if (!Set("ll", "rl").contains(stateRoles(s)))
            true
          else
            outgoingTransitions
              .getOrElse(s, Seq.empty)
              .exists(t =>
                t.label == label &&
                  t.step == Left &&
                  t.targets.forall(state.contains)
              )
        }

        def satisfiesLeftPredecessors(s: Int): Boolean = {
          if (!Set("rl", "rr", "rf").contains(stateRoles(s)))
            true
          else
            incomingTransitions
              .getOrElse(s, Seq.empty)
              .exists { case (source, transition) =>
                state.contains(source) &&
                  transition.label == label &&
                  transition.step == Right &&
                  transition.targets.forall(nextState.contains)
              }
        }

        // condition 4:
        // successor must not contain ir or lr states
        nextState = nextState.filterNot { s =>
          Set("ir", "lr").contains(stateRoles(s))
        }

        nextState = nextState.filter { s =>
          satisfiesLeftSuccessors(s) &&
            satisfiesLeftPredecessors(s)
        }

        edges.add(Edge(state, label, nextState))
        schedule(nextState)
      }
    }
  }

  private val activeWorkers = new AtomicInteger(0)

  private def buildAutomaton(): BricsAutomaton = {
    val builder = new BricsAutomatonBuilder

    val stateMap = mutable.HashMap[MacroState, BricsAutomaton#State]()

    val epsilons =
      new MHashMap[BricsAutomaton#State, MSet[BricsAutomaton#State]]
        with MultiMap[BricsAutomaton#State, BricsAutomaton#State]

    val discoveredIt = discovered.iterator()

    while (discoveredIt.hasNext) {
      val macroState = discoveredIt.next()
      val bricsState = builder.getNewState

      stateMap += macroState -> bricsState

      if (macroState.subsetOf(afa.rfStates))
        builder.setAccept(bricsState, true)
    }

    builder.setInitialState(
      stateMap(afa.initialStates.toSet)
    )

    val edgeIt = edges.iterator()

    while (edgeIt.hasNext) {
      val edge = edgeIt.next()

      builder.addTransition(
        stateMap(edge.from),
        (edge.label.toChar, edge.label.toChar),
        stateMap(edge.to)
      )
    }

    val epsilonIt = epsilonEdges.iterator()

    while (epsilonIt.hasNext) {
      val edge = epsilonIt.next()

      epsilons.addBinding(
        stateMap(edge.from),
        stateMap(edge.to)
      )
    }

    AutomataUtils.buildEpsilons(builder, epsilons)

    builder.getAutomaton
  }

  def run() {
    val executor = Executors.newFixedThreadPool(numWorkers)

    // initial macro state
    schedule(afa.initialStates.toSet)

    for (_ <- 0 until numWorkers) {
      executor.submit(new Runnable {
        override def run(): Unit = {
          var running = true

          while (running) {
            val state = workQueue.poll(100, TimeUnit.MILLISECONDS)

            if (state != null) {
              activeWorkers.incrementAndGet()

              try {
                expand(state)
              } finally {
                activeWorkers.decrementAndGet()
              }
            } else {
              // no queued work and nobody is currently producing new work
              if (workQueue.isEmpty && activeWorkers.get() == 0)
                running = false
            }
          }
        }
      })
    }

    executor.shutdown()
    executor.awaitTermination(Long.MaxValue, TimeUnit.NANOSECONDS)
  }

  def result: BricsAutomaton = {
    run()
    buildAutomaton()
  }
}
