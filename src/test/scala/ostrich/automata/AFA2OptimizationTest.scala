package ostrich.automata.afa2.concrete

import ostrich.automata.afa2.{Right, Left, StepTransition}
import org.scalacheck.Properties

object AFA2OptimizationTest extends Properties("AFA2") {

  // get a random 2AFA
  // we build a automaton that is allready categorized
  // we do this by only using right-transitions
  // this also avoids looping
  // also initial states ony have outgoing transitions
  // and final states only incoming ones
  private def randomAFA2(seed: Long, stateCount: Int = 20,
  alphabet: IndexedSeq[Int] = Vector('a'.toInt, 'b'.toInt),
  maxTargetCount: Int = 4, universalProbability: Double = 0.2): AFA2 = {

    val random = new scala.util.Random(seed)
    val states = Seq.range(0, stateCount)

    // first state is the initial state
    val initialState = 0
    val initialStates = Seq(initialState)

    // last state is the final state
    // NFA translator seems to struggle if it has outgoing transitions
    val finalState = stateCount - 1
    val finalStates = Seq(finalState)

    // get random transitions
    var transitions = Map[Int, Seq[StepTransition]]()

    // iterate all states and labels
    for (state <- states) {
      // skip initial and final
      if (state != finalState && state != initialState)
      {
        var outgoing = Seq[StepTransition]()

        for (label <- alphabet) {
          val targets = randomTargets(random, stateCount, maxTargetCount, universalProbability)
          outgoing = outgoing :+ StepTransition(label, Right, targets)
        }

        transitions = transitions + (state -> outgoing)
      }
    }

    // force initial state to enter the automaton
    transitions = transitions + (
      initialState -> Seq(
        StepTransition('a'.toInt, Right, Seq(1)),
        StepTransition('b'.toInt, Right, Seq(1))))

    // force the state before final to reach final
    val stateBeforeFinal = stateCount - 2
    transitions = transitions + (
      stateBeforeFinal -> Seq(
        StepTransition('a'.toInt, Right, Seq(finalState)),
        StepTransition('b'.toInt, Right, Seq(finalState))))

    AFA2(initialStates, finalStates, transitions)
  }

  private def randomTargets(random: scala.util.Random, stateCount: Int,
  maxTargetCount: Int, universalProbability: Double): Seq[Int] = {
    // one target / existential transition
    var targetCount = 1

    // universal branching
    if (random.nextDouble() < universalProbability) {
      targetCount = 2 + random.nextInt(maxTargetCount - 1)
    }

    var targets = Seq[Int]()
    while (targets.size < targetCount) {
      val target = random.nextInt(stateCount)

      if (!targets.contains(target)) {
        targets = targets :+ target
      }
    }

    targets
  }

  property("partitionRefinement preserves language (hand crafted test)") = {
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

    val reduced = aut.partitionRefinement()

    val beforeNFA =
      NFATranslator(AFA2StateDuplicator(aut), null)

    val afterNFA =
      NFATranslator(AFA2StateDuplicator(reduced), null)

    val beforeMinusAfter = beforeNFA & !afterNFA
    val afterMinusBefore = afterNFA & !beforeNFA

    reduced.states.size < aut.states.size &&
      beforeMinusAfter.isEmpty &&
      afterMinusBefore.isEmpty
  }

  // TODO: This test shows that not any 2AFA can be tranfomed to a S2AFA by AFA2StateDuplicator
  // TODO: This makes all optimizations dangerous, I have to adjust the translation
  // TODO: Maybe partition refinement also produces a inlvaid 2AFA somehow? I have to check
  property("partitionRefinement preserves language (100 random automata)") = {
    var allEquivalent = true
    var seed = 0L

    println("Starting loop...")
    while (seed < 100L && allEquivalent) {
      val aut = randomAFA2(seed)
      val reduced = aut.partitionRefinement()

      println("Got both automata, now translating them to NFAs...")
      val beforeNFA =
        NFATranslator(AFA2StateDuplicator(aut), null)

      val afterNFA =
        NFATranslator(AFA2StateDuplicator(reduced), null)

      println("Got the NFAs, now checking...")
      val beforeMinusAfter = beforeNFA & !afterNFA
      val afterMinusBefore = afterNFA & !beforeNFA

      val equivalent =
        beforeMinusAfter.isEmpty && afterMinusBefore.isEmpty

      if (!equivalent) {
        println("Counterexample seed: " + seed)
        println("Original AFA2:")
        println(aut)
        println("Reduced AFA2:")
        println(reduced)
        allEquivalent = false
      }

      seed = seed + 1L
      println(seed + "/100 checked")
    }

    allEquivalent
  }
}