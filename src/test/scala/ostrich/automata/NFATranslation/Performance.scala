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
import ostrich.automata.NFATranslation.Correctness.property
import ostrich.automata.afa2.concrete.{AFA2, AFA2StateDuplicator, AFA2StateExpander, AFA2TestHelper}
import ostrich.automata.afa2.symbolic.{SymbEpsReducer, SymbToConcTranslator}
import ostrich.automata.{ECMAToSymbAFA2, Regex2Aut}
import ostrich.{ECMARegexParser, OFlags, OstrichStringTheory}

object Performance extends Properties("AFA2") {

  property("StateExpander performs max 20% worse then StateDuplicator (250 random automata)") = {
    val automataCount = 250L
    var seed = 0L

    var totalOriginalStates = 0
    var totalDuplicatorStates = 0
    var totalExpanderStates = 0

    while (seed < automataCount) {
      val aut = AFA2TestHelper.randomAFA2(seed)
      val expander = AFA2StateExpander(aut)
      val duplicator = AFA2StateDuplicator(aut)

      totalOriginalStates += aut.states.size
      totalExpanderStates += expander.states.size
      totalDuplicatorStates += duplicator.states.size

      seed = seed + 1L
    }

    println("Original:" + totalOriginalStates)
    println("Expander:" + totalExpanderStates)
    println("Duplicator:" + totalDuplicatorStates)

    // 20% increase is fine
    totalExpanderStates < totalDuplicatorStates * 1.2
  }

  property("StateExpander performs max 20% worse then StateDuplicator (ECMA regex automata)") = {
    val regexes = AFA2TestHelper.regexes
    val automataCount = regexes.size
    var regexIndex = 0

    var totalOriginalStates = 0
    var totalDuplicatorStates = 0
    var totalExpanderStates = 0

    while (regexIndex < automataCount) {
      val regex = regexes(regexIndex)
      val aut = AFA2TestHelper.ecmaRegexToConcreteAFA2(regex)
      val expander = AFA2StateExpander(aut)
      val duplicator = AFA2StateDuplicator(aut)

      totalOriginalStates += aut.states.size
      totalExpanderStates += expander.states.size
      totalDuplicatorStates += duplicator.states.size

      regexIndex = regexIndex + 1
    }

    println("Original:" + totalOriginalStates)
    println("Expander:" + totalExpanderStates)
    println("Duplicator:" + totalDuplicatorStates)

    // 20% increase is fine
    totalExpanderStates < totalDuplicatorStates * 1.2
  }
}