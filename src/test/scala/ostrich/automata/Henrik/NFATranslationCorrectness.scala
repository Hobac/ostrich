package ostrich.automata.Henrik

import org.scalacheck.Properties
import ostrich.automata.afa2.concrete.{AFA2StateDuplicator, AFA2StateExpander, AFA2TestHelper, NFAParallelTranslator, NFATranslator}

object NFATranslationCorrectness extends Properties("AFA2") {

  property("NFAParallelTranslator tested against LazyNFATranslator (1000 random automata)") = {
    val automataCount = 1000L
    var seed = 0L

    var allEquivalent = true
    while (seed < automataCount && allEquivalent) {
      val aut = AFA2TestHelper.randomAFA2(seed)
      var safa = AFA2StateDuplicator(aut)
      val parallel = NFAParallelTranslator(AFA2StateDuplicator(safa))
      val lazyTown = NFATranslator(AFA2StateDuplicator(safa), null)

      val parallelMinusLazyTown = parallel & !lazyTown
      val lazyTownMinusParallel = lazyTown & !parallel

      val equivalent = parallelMinusLazyTown.isEmpty && lazyTownMinusParallel.isEmpty

      if (!equivalent) {
        println("Counterexample seed: " + seed)
        println(aut)
        allEquivalent = false
      }

      seed = seed + 1L
    }

    allEquivalent
  }
}