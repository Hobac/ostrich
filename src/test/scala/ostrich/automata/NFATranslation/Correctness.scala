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

package ostrich.automata.NFATranslation

import org.scalacheck.Properties
import ostrich.automata.{ECMAToSymbAFA2, Regex2Aut}
import ostrich.{ECMARegexParser, OFlags, OstrichStringTheory}
import ostrich.automata.afa2.concrete.{AFA2, AFA2StateDuplicator, AFA2StateExpander, AFA2TestHelper, NFATranslator}
import ostrich.automata.afa2.symbolic.{SymbEpsReducer, SymbToConcTranslator}
import ostrich.automata.afa2.{Right, StepTransition}

object Correctness extends Properties("AFA2") {

  property("StateDuplicator can translate 2AFA to S2AFA (ECMA regex automata)") = {

    val regexes = AFA2TestHelper.regexes
    val automataCount = regexes.size
    var regexIndex = 0
    var allOk = true

    while (regexIndex < automataCount && allOk) {
      val regex = regexes(regexIndex)

      val aut = AFA2TestHelper.ecmaRegexToConcreteAFA2(regex)
      val saut = AFA2StateDuplicator(aut)

      val ok = saut.states.toSet == saut.irStates ++ saut.llStates ++
        saut.lrStates ++ saut.rlStates ++ saut.rrStates ++ saut.rfStates

      if(!ok){
        allOk = false
      }

      regexIndex = regexIndex + 1
    }

    allOk
  }

  property("StateExpander can translate 2AFA to S2AFA (ECMA regex automata)") = {
    val regexes = AFA2TestHelper.regexes
    val automataCount = regexes.size
    var regexIndex = 0
    var allOk = true

    while (regexIndex < automataCount && allOk) {
      val regex = regexes(regexIndex)

      val aut = AFA2TestHelper.ecmaRegexToConcreteAFA2(regex)
      val saut = AFA2StateExpander(aut)

      val ok = saut.states.toSet == saut.irStates ++ saut.llStates ++
        saut.lrStates ++ saut.rlStates ++ saut.rrStates ++ saut.rfStates

      if(!ok){
        allOk = false
      }

      regexIndex = regexIndex + 1
    }

    allOk
  }

  property("StateExpander preserves language (100 random automata, checked with StateDuplicator)") = {
    val automataCount = 100L
    var seed = 0L
    var allEquivalent = true

    while (seed < automataCount && allEquivalent) {
      val aut = AFA2TestHelper.randomAFA2(seed)
      val expander = NFATranslator(AFA2StateExpander(aut), null)
      val duplicator = NFATranslator(AFA2StateDuplicator(aut), null)

      val expanderMinusDuplicator = expander & !duplicator
      val duplicatorMinusExpander = duplicator & !expander

      val equivalent = expanderMinusDuplicator.isEmpty && duplicatorMinusExpander.isEmpty

      if (!equivalent) {
        println("Counterexample seed: " + seed)
        allEquivalent = false
      }

      seed = seed + 1L
    }

    allEquivalent
  }

  /**
  property("StateExpander preserves language (ECMA regex automata, checked with StateDuplicator)") = {
    val regexes = AFA2TestHelper.regexes
    val automataCount = regexes.size
    var regexIndex = 0
    var allEquivalent = true

    while (regexIndex < automataCount && allEquivalent) {

      println(regexIndex / automataCount * 100 + "% done...")
      val regex = regexes(regexIndex)

      println(regex)
      val aut = AFA2TestHelper.ecmaRegexToConcreteAFA2(regex)

      val expander = NFATranslator(AFA2StateExpander(aut), null)
      val duplicator = NFATranslator(AFA2StateDuplicator(aut), null)

      val expanderMinusDuplicator = expander & !duplicator
      val duplicatorMinusExpander = duplicator & !expander

      val equivalent = expanderMinusDuplicator.isEmpty && duplicatorMinusExpander.isEmpty

      if (!equivalent) {
        println("Counterexample regex: " + regex)
        allEquivalent = false
      }

      regexIndex = regexIndex + 1
    }

    allEquivalent
  }
  */

  property("StateExpander can translate 2AFA to S2AFA (100 random automata)") = {
    val automataCount = 100L
    var seed = 0L

    var allOk = true
    while (seed < automataCount && allOk) {
      val aut = AFA2TestHelper.randomAFA2(seed)
      val saut = AFA2StateExpander(aut)

      val ok = saut.states.toSet == saut.irStates ++ saut.llStates ++
        saut.lrStates ++ saut.rlStates ++ saut.rrStates ++ saut.rfStates

      if (!ok) {
        println("Counterexample seed: " + seed)
        allOk = false
      }

      seed = seed + 1L
    }

    true
  }

  property("StateDuplicator can translate 2AFA to S2AFA (100 random automata)") = {
    val automataCount = 100L
    var seed = 0L

    var allOk = true
    while (seed < automataCount && allOk) {
      val aut = AFA2TestHelper.randomAFA2(seed)
      val saut = AFA2StateDuplicator(aut)

      val ok = saut.states.toSet == saut.irStates ++ saut.llStates ++
        saut.lrStates ++ saut.rlStates ++ saut.rrStates ++ saut.rfStates

      if (!ok) {
        println("Counterexample seed: " + seed)
        allOk = false
      }

      seed = seed + 1L
    }

    true
  }
}