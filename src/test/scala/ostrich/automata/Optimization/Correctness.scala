package ostrich.automata.Optimization

import org.scalacheck.Properties
import ostrich.automata.afa2.concrete.{AFA2, AFA2StateDuplicator, AFA2StateExpander, AFA2TestHelper, NFATranslator}
import ostrich.automata.afa2.{Right, StepTransition}

object Correctness extends Properties("AFA2") {

  property("optimizeUntilFixpoint() preserves language (hand crafted test)") = {
    val aut = AFA2(
      initialStates = Seq(0),
      finalStates = Seq(9),
      transitions = Map(
        0 -> Seq(
          StepTransition('a'.toInt, Right, Seq(1)),
          StepTransition('b'.toInt, Right, Seq(2))
        ),

        // 1 and 3 are intentionally equivalent
        1 -> Seq(
          StepTransition('a'.toInt, Right, Seq(3)),
          StepTransition('b'.toInt, Right, Seq(4))
        ),
        3 -> Seq(
          StepTransition('a'.toInt, Right, Seq(3)),
          StepTransition('b'.toInt, Right, Seq(4))
        ),

        // 2 and 5 are intentionally equivalent
        2 -> Seq(
          StepTransition('a'.toInt, Right, Seq(5)),
          StepTransition('b'.toInt, Right, Seq(6))
        ),
        5 -> Seq(
          StepTransition('a'.toInt, Right, Seq(5)),
          StepTransition('b'.toInt, Right, Seq(6))
        ),

        // 4 and 7 are intentionally equivalent
        4 -> Seq(
          StepTransition('a'.toInt, Right, Seq(7)),
          StepTransition('b'.toInt, Right, Seq(9))
        ),
        7 -> Seq(
          StepTransition('a'.toInt, Right, Seq(7)),
          StepTransition('b'.toInt, Right, Seq(9))
        ),

        // 6 and 8 are intentionally equivalent
        6 -> Seq(
          StepTransition('a'.toInt, Right, Seq(8)),
          StepTransition('b'.toInt, Right, Seq(9))
        ),
        8 -> Seq(
          StepTransition('a'.toInt, Right, Seq(8)),
          StepTransition('b'.toInt, Right, Seq(9))
        )
      )
    )

    val reduced = aut.optimizeUntilFixpoint()
    val beforeNFA = NFATranslator(AFA2StateExpander(aut), null)
    val afterNFA = NFATranslator(AFA2StateExpander(reduced), null)

    val beforeMinusAfter = beforeNFA & !afterNFA
    val afterMinusBefore = afterNFA & !beforeNFA

    reduced.states.size < aut.states.size &&
      beforeMinusAfter.isEmpty &&
      afterMinusBefore.isEmpty
  }

  property("optimizeUntilFixpoint() preserves language (1000 random automata)") = {
    val automataCount = 1000L
    var seed = 0L

    var allEquivalent = true
    while (seed < automataCount && allEquivalent) {
      val aut = AFA2TestHelper.randomAFA2(seed)
      val reduced = aut.optimizeUntilFixpoint()

      val beforeNFA = NFATranslator(AFA2StateExpander(aut), null)
      val afterNFA = NFATranslator(AFA2StateExpander(reduced), null)

      val beforeMinusAfter = beforeNFA & !afterNFA
      val afterMinusBefore = afterNFA & !beforeNFA

      val equivalent = beforeMinusAfter.isEmpty && afterMinusBefore.isEmpty

      if (!equivalent) {
        println("Counterexample seed: " + seed)
        println("Original AFA2:")
        println(aut)
        println("Reduced AFA2:")
        println(reduced)
        allEquivalent = false
      }

      seed = seed + 1L
    }

    allEquivalent
  }
}