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

package ostrich.automata.Optimization

import org.scalacheck.Properties
import ostrich.automata.NFATranslation.Performance.property
import ostrich.automata.afa2.concrete.{AFA2StateDuplicator, AFA2StateExpander, AFA2TestHelper}

object Performance extends Properties("AFA2") {

  /**
  property("StateExpander + optimizeUntilFixpoint() outperforms StateDuplicator + minimizeStates() (ECMA regex automata)") = {
    val regexes = AFA2TestHelper.regexes.take(10)
    val automataCount = regexes.size
    var regexIndex = 0

    var totalOriginalStates = 0
    var totalDuplicatorStates = 0
    var totalExpanderStates = 0

    while (regexIndex < automataCount) {
      val regex = regexes(regexIndex)
      val aut = AFA2TestHelper.ecmaRegexToConcreteAFA2(regex)

      // can take any 2AFA and convert it but can lead to bigger automata
      val expander = AFA2StateExpander(aut.optimizeUntilFixpoint())

      // can only accept a subclass but leads to smaller automata
      val duplicator = AFA2StateDuplicator(aut.minimizeStates())

      totalOriginalStates += aut.states.size
      totalExpanderStates += expander.states.size
      totalDuplicatorStates += duplicator.states.size

      regexIndex = regexIndex + 1
    }

    println("Original:" + totalOriginalStates)
    println("Expander:" + totalExpanderStates)
    println("Duplicator:" + totalDuplicatorStates)

    totalExpanderStates < totalDuplicatorStates
  }
  */

  property("StateExpander + optimizeUntilFixpoint() outperforms StateDuplicator + minimizeStates() (250 random automata)") = {
    val automataCount = 250L
    var seed = 0L

    var totalOriginalStates = 0
    var totalDuplicatorStates = 0
    var totalExpanderStates = 0

    while (seed < automataCount) {
      val aut = AFA2TestHelper.randomAFA2(seed)

      val duplicator = AFA2StateDuplicator(aut.minimizeStates())
      val expander = AFA2StateExpander(aut.optimizeUntilFixpoint())

      totalOriginalStates += aut.states.size
      totalExpanderStates += expander.states.size
      totalDuplicatorStates += duplicator.states.size

      seed = seed + 1L
    }

    println("Original:" + totalOriginalStates)
    println("Expander:" + totalExpanderStates)
    println("Duplicator:" + totalDuplicatorStates)

    totalExpanderStates < totalDuplicatorStates
  }

  property("optimizeUntilFixpoint() outperforms minimizeStates() in 2AFA state reduction (250 random automata)") = {
    val automataCount = 250L
    var seed = 0L

    var totalOriginalStates = 0
    var totalMinimizedStates = 0
    var totalOptimizeUntilFixpointStates = 0
    var optimizeUntilFixpointBetter = 0
    var minimizeStatesBetter = 0
    var bothSame = 0

    while (seed < automataCount) {
      val automaton = AFA2TestHelper.randomAFA2(seed)

      val minimizedAutomaton = automaton.minimizeStates()
      val partitionRefinedAutomaton = automaton.optimizeUntilFixpoint()

      val originalStateCount = automaton.states.size
      val minimizedStateCount = minimizedAutomaton.states.size
      val partitionRefinedStateCount = partitionRefinedAutomaton.states.size

      totalOriginalStates = totalOriginalStates + originalStateCount
      totalMinimizedStates = totalMinimizedStates + minimizedStateCount
      totalOptimizeUntilFixpointStates = totalOptimizeUntilFixpointStates + partitionRefinedStateCount

      if (partitionRefinedStateCount < minimizedStateCount) {
        optimizeUntilFixpointBetter = optimizeUntilFixpointBetter + 1
      } else if (minimizedStateCount < partitionRefinedStateCount) {
        minimizeStatesBetter = minimizeStatesBetter + 1
      } else {
        bothSame = bothSame + 1
      }

      seed = seed + 1L
    }

    val minimizeStatesReduction =
      100.0 - (totalMinimizedStates.toDouble * 100.0 / totalOriginalStates.toDouble)

    val optimizeUntilFixpointReduction =
      100.0 - (totalOptimizeUntilFixpointStates.toDouble * 100.0 / totalOriginalStates.toDouble)

    println("Compared " + automataCount + " random automata")
    println("Original total states: " + totalOriginalStates)
    println("minimizeStates total states: " + totalMinimizedStates)
    println("optimizeUntilFixpoint total states: " + totalOptimizeUntilFixpointStates)

    println("minimizeStates reduction: " + minimizeStatesReduction + "%")
    println("optimizeUntilFixpoint reduction: " + optimizeUntilFixpointReduction + "%")

    println("optimizeUntilFixpoint produced smaller automata in " + optimizeUntilFixpointBetter + " cases")
    println("minimizeStates produced smaller automata in " + minimizeStatesBetter + " cases")
    println("Both produced same-size automata in " + bothSame + " cases")

    optimizeUntilFixpointReduction >= 0.0
  }
}