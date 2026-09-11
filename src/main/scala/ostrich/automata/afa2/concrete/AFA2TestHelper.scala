package ostrich.automata.afa2.concrete

import ostrich.automata.afa2.symbolic.{SymbEpsReducer, SymbToConcTranslator}
import ostrich.automata.{ECMAToSymbAFA2, Regex2Aut}
import ostrich.{ECMARegexParser, OFlags, OstrichStringTheory}
import ostrich.automata.afa2.{Right, Left, Step, StepTransition}

object AFA2TestHelper  {
  /** Might also generate a smaller automaton then stateCount! */
  def superRandomAFA2(
                  seed: Long,
                  stateCount: Int,
                  maxTargetCount: Int = 2,
                  maxTransitionsPerState: Int = 2,
                  universalProbability: Double = 0.2,
                  leftProbability: Double = 0.2,
                  alphabet: IndexedSeq[Int] = Vector('a'.toInt, 'b'.toInt)
                ): AFA2 = {

    val random = new scala.util.Random(seed)

    val initialStates = Seq(0)
    val finalStates = Seq(stateCount - 1)

    var transitions = Map[Int, Seq[StepTransition]]()

    for (state <- 0 until stateCount) {
      var outgoingTransitions = Seq[StepTransition]()
      val transitionCount = random.nextInt(maxTransitionsPerState)

      for (_ <- 0 until transitionCount) {
        val label = alphabet(random.nextInt(alphabet.size))
        val direction: Step = if (random.nextDouble() < leftProbability) Left else Right
        val targetCount =
          if (random.nextDouble() < universalProbability)
            2 + random.nextInt(maxTargetCount - 1)
          else
            1

        val targets = Seq.fill(targetCount)(random.nextInt(stateCount)).distinct
        outgoingTransitions :+= StepTransition(
          label,
          direction,
          targets
        )
      }

      transitions += state -> outgoingTransitions
    }

    // force one transition to make the initial and final state valid
    transitions += 0 -> Seq(StepTransition(alphabet(0), Right, Seq(stateCount - 1)))

    AFA2(initialStates, finalStates, transitions).restrictToReachableStates
  }

  // get a random 2AFA
  // we only use right-transitions
  // this avoids looping
  // the initial state only has outgoing transitions
  // the final state only incoming ones
  // so that StateDuplicator does not have any issues
  // we also remove all non-reachable state so that StateDuplicator does not have any issues
  def randomAFA2(
                          seed: Long,
                          stateCount: Int = 50,
                          maxTargetCount: Int = 3,
                          universalProbability: Double = 0.2,
                          alphabet: IndexedSeq[Int] = Vector('a'.toInt, 'b'.toInt, 'c'.toInt)
                        ): AFA2 = {

    val random = new scala.util.Random(seed)

    val initialState = 0
    val finalState = stateCount - 1

    val initialStates = Seq(initialState)
    val finalStates = Seq(finalState)

    var transitions = Map[Int, Seq[StepTransition]]()

    // get random transitions
    for (state <- 0 until finalState) {
      var outgoingTransitions = Seq[StepTransition]()

      var attempt = 0
      while (attempt < 5) {
        if (random.nextDouble() <= 0.5) {
          val label = alphabet(random.nextInt(alphabet.size))

          val targets =
            randomForwardTargets(
              random = random,
              currentState = state,
              finalState = finalState,
              maxTargetCount = maxTargetCount,
              universalProbability = universalProbability
            )

          val transition = StepTransition(label, Right, targets)
          outgoingTransitions = outgoingTransitions :+ transition
        }

        attempt += 1
      }

      // at least one outgoing transition is needed
      if (outgoingTransitions.isEmpty) {
        val transition = StepTransition('a'.toInt, Right, Seq(state + 1))
        outgoingTransitions = outgoingTransitions :+ transition
      }

      transitions = transitions + (state -> outgoingTransitions)
    }

    AFA2(initialStates, finalStates, transitions).restrictToReachableStates
  }

  def randomForwardTargets(
                                    random: scala.util.Random,
                                    currentState: Int,
                                    finalState: Int,
                                    maxTargetCount: Int,
                                    universalProbability: Double
                                  ): Seq[Int] = {

    val firstPossibleTarget = currentState + 1
    val possibleTargets = firstPossibleTarget to finalState
    var targetCount = 1

    if (random.nextDouble() < universalProbability) {
      targetCount = 2 + random.nextInt(maxTargetCount - 1)
    }

    if (targetCount > possibleTargets.size) {
      targetCount = possibleTargets.size
    }

    var targets = Seq[Int]()

    while (targets.size < targetCount) {
      val randomIndex = random.nextInt(possibleTargets.size)
      val target = possibleTargets(randomIndex)

      if (!targets.contains(target)) {
        targets = targets :+ target
      }
    }

    targets
  }

  val regexes = Seq(
    "a*b",
    "(ab|cd)*ef",
    "[a-zA-Z_][a-zA-Z0-9_]*",
    "(a|aa)*b",
    "(ab|ac|ad){1,3}e",
    "([0-9]{2,4}|[a-f]+)z",
    "a(?=b)",
    "(?<=a)b",
    "\\b[a-z]+\\b",
    "(foo|bar|baz).*qux",
    "abc",
    "a|b|c",
    "(a|b)*c",
    "ab+c?",
    "a{2,5}b",
    "(ab){2,4}",
    "[0-9]+",
    "[a-fA-F0-9]{8}",
    "[^abc]*d",
    "hello|world",
    "(cat|car|cart)",
    "(foo|foobar|foobaz)",
    "colou?r",
    "gr(a|e)y",
    "https?://[a-z]+\\.[a-z]+",
    "[a-z]{3}[0-9]{2}",
    "([a-z]+|[0-9]+)*",
    "(a|b|c){1,4}",
    "(ab|ba|aa|bb)*",
    "([A-Z][a-z]+)( [A-Z][a-z]+)*",
    "^abc",
    "abc$",
    "^abc$",
    "^.*abc.*$",
    "(?=abc)abc",
    "abc(?=def)",
    "abc(?!def)",
    "(?<!a)b",
    "(?<=foo)bar",
    "foo(?=bar)",
    "foo(?!bar)",
    "\\bword\\b",
    "\\Bword\\B",
    "\\b[a-zA-Z_][a-zA-Z0-9_]*\\b",
    "(a*)*b",
    "(a|ab|abc)*d",
    "((ab|cd)ef)*",
    "(a|b)*(c|d)*",
    "([0-9]{1,3}\\.){3}[0-9]{1,3}",
    "[a-z]+@[a-z]+\\.[a-z]{2,4}",
    "(0|[1-9][0-9]*)",
    "-?(0|[1-9][0-9]*)(\\.[0-9]+)?",
    "(true|false|null)",
    "\"[^\"]*\"",
    "(aa|aaa|aaaa)*b",
    "(ab|abc|abcd|abcde)",
    "([ab]{2}|[bc]{2}|[cd]{2})*",
    "(x|xy|xyz){1,3}z",
    "([a-c]|[b-d]|[c-e])*",
    "(foo|bar){2,5}",
    "(a(b|c)d|ab(cd|ef))",
    "((a|b)c|(a|b)d)*",
    "([0-9]|[1-9][0-9]|100)",
    "(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)",
    ".*",
    ".+",
    ".{2,5}",
    "a.*b.*c",
    "[\\s\\S]*",
    "\\d+",
    "\\w+",
    "\\s*abc\\s*",
    "(\\w+\\.)*\\w+",
    "(\\d{4}-\\d{2}-\\d{2})"
  )

  // TODO: Check if this is correct
  def ecmaRegexToConcreteAFA2(regex: String): AFA2 = {
    val theory =
      new OstrichStringTheory(
        Seq(),
        OFlags(regexTranslator = OFlags.RegexTranslator.Complete)
      )

    val parser = new ECMARegexParser(theory)

    val exactRegexTerm =
      parser.string2TermExact(regex)

    val syntacticTransformations =
      new Regex2Aut.SyntacticTransformations(theory, parser)

    val normalizedRegexTerm =
      syntacticTransformations(exactRegexTerm)

    val ecmaToAFA =
      new ECMAToSymbAFA2(theory, parser)

    val extendedSymbolicAFA =
      ecmaToAFA.toSymbExt2AFA(normalizedRegexTerm)

    val epsReducer =
      new SymbEpsReducer(theory, extendedSymbolicAFA)

    val symbolicAFA =
      epsReducer.afa

    val concreteTranslator =
      new SymbToConcTranslator(symbolicAFA)

    concreteTranslator.forth().restrictToReachableStates
  }
}