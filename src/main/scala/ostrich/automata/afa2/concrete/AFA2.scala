/**
 * This file is part of Ostrich, an SMT solver for strings.
 * Copyright (c) 2022-2023 Riccado De Masellis, Philipp Ruemmer. All rights reserved.
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

import ostrich.automata.afa2.{Left, Right, Step, StepTransition}

import java.nio.file.Path
import scala.collection.mutable
import scala.collection.mutable.{HashSet => MHashSet}

/*
 * Existential nondeterminism is implemented by having multiple
 * transitions in the sequence.  Universal nondeterminism is
 * implemented by having multiple target states in Transition.
 */


/*
 * Class AFA2 implements a concrete 2AFA with:
 * - only concrete transitions;
 * - no epsilon transitions;
 * - accepting only at the end of the string.
 * 
 * This class is used as input for the 2AFA -> NFA translation.
 */
case class AFA2(initialStates : Seq[Int],
                finalStates   : Seq[Int],
                transitions   : Map[Int, Seq[StepTransition]]) {

  override def toString: String = {
    val res = new mutable.StringBuilder()
    res.append("Initial states: " + initialStates + "\n")
    res.append("Final states: " + finalStates + "\n")
    for (tr <- transitions) {
      res.append(tr._1 + "goes to \n")
      for (t <- tr._2) res.append(t)
    }
    res.toString()
  }

  assert(!initialStates.isEmpty)

  val states = {
    val states = new MHashSet[Int]

    states ++= initialStates
    states ++= finalStates

    for ((source, ts)                  <- transitions.iterator;
         StepTransition(_, _, targets) <- ts.iterator;
         target                        <- targets.iterator) {
      states += source
      states += target
    }

    states.toIndexedSeq.sorted
  }

  lazy val fwdReachable = {
    val reachable = new MHashSet[Int]
    reachable ++= initialStates

    var oldSize = 0
    while (oldSize < reachable.size) {
      oldSize = reachable.size

      for (s                             <- reachable.toList;
           StepTransition(_, _, targets) <- transitions.getOrElse(s, List())) {
        reachable ++= targets
      }
    }

    reachable.toSet
  }

  lazy val bwdReachable = {
    val reachable = new MHashSet[Int]
    reachable ++= finalStates

    var oldSize = 0
    while (oldSize < reachable.size) {
      oldSize = reachable.size

      for ((source, ts)                  <- transitions.iterator;
           if !(reachable contains source);
           StepTransition(_, _, targets) <- ts.iterator)
        if (targets forall reachable)
          reachable += source
    }

    reachable.toSet
  }

  lazy val reachableStates =
    fwdReachable & bwdReachable


  /*
   * Minimizes the states by merging states that have the same
   * outgoing transitions to the same states.  It performs
   * minimizeStatesStep until the fixpoint (of not being able to
   * remove any more states) is reached.
   */
  def minimizeStates() : AFA2 = {

    def minimizeStatesStep(aut: AFA2): AFA2 = {

      val flatTrans = for ((st, ts) <- aut.transitions.toSeq) yield (ts.toSet, st)

      // Map keeping track of eliminatedState => stateKept
      val stateMap = mutable.HashMap[Int, Int]()

      val transStateMap = flatTrans.groupBy(_._1).mapValues(l => l map (_._2))
      //println("transStateMap:\n" + transStateMap)
      /*
    The above map is still rough, as in the values can contain states that are final, nonfinal, noninitial, initial
    We have to split them in group of states:
    - plain : neither final nor initial
    - fi : final and initial
    - f : final
    - i : initial
     */
      var plainTSM = transStateMap.mapValues(_.filter(x => !aut.initialStates.contains(x) && !aut.finalStates.contains(x)))
      var fiTSM = transStateMap.mapValues(_.filter(x => aut.initialStates.contains(x) && aut.finalStates.contains(x)))
      var fTSM = transStateMap.mapValues(_.filter(x => !aut.initialStates.contains(x) && aut.finalStates.contains(x)))
      var iTSM = transStateMap.mapValues(_.filter(x => aut.initialStates.contains(x) && !aut.finalStates.contains(x)))

      plainTSM = plainTSM.filter(_._2.nonEmpty)
      fiTSM = fiTSM.filter(_._2.nonEmpty)
      fTSM = fTSM.filter(_._2.nonEmpty)
      iTSM = iTSM.filter(_._2.nonEmpty)

      //println("plainTSM:\n" + plainTSM)
      //println("fiTSM:\n" + fiTSM)
      //println("fTSM:\n" + fTSM)
      //println("iTSM:\n" + iTSM)


      for ((_, sts) <- plainTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- fiTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- fTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- iTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      /* Now in the keyset of StateMap contains all and only states that has to be removed.
    The removal strategy is the following:
    (1) filter the transitions map with states to be removed;
    (2) scan such reduced transitions and map the arrival states with stateMap
     */
      val toBeRemoved = stateMap.keySet.toSet
      //println("Removed map:\n" + stateMap)
      //println("To be removed:\n" + toBeRemoved)
      // All other states have to be mapped to themsleves!
      for (s <- aut.states.toSet -- toBeRemoved) stateMap += ((s, s))
      val reducedTrans = aut.transitions.filterNot(x => toBeRemoved.contains(x._1))
      //println("Reduced trans:\n" + reducedTrans)
      val newTrans = reducedTrans.mapValues(_.map(x => StepTransition(x.label, x.step, x.targets.map(stateMap))))

      val newAut = AFA2(aut.initialStates, aut.finalStates, newTrans.toMap)

      newAut.restrictToReachableStates
    }

    /*
    Similar to the one before but trying to take into account self-loop as explained below.
    Currently not used as not extensively tested (but should work). Not much difference with the non-optimized verson.
     */
    def minimizeStatesStepOptimised(aut: AFA2) : AFA2 = {

      //val flatTrans = for ((st, ts) <- aut.transitions.toSeq) yield (ts.toSet, st)
      /*
      Problem: self-transitions do not allow to easily recognise states that have the same outgoing transitions.
      Therefore, is we have a self transition (7, StepTrans(->, [5], Seq(7))) we substitute it with
      (7, StepTrans(->, [5], Seq(SELF))) so they can be recognised.
       */
      val SELF = -5
      val aux = for ((st, ts) <- aut.transitions.toSeq) yield (ts.toSet, st)

      val flatTrans = aux.map{case (transSet, state) =>
        val selfMap: Map[Int, Int] = (for (s <- aut.states) yield (if (s==state) (s, SELF) else (s, s))).toMap
        val newTransSet = transSet.map(x => StepTransition(x.label, x.step, x.targets.map(selfMap)))
        (newTransSet, state)
      }

      // Map keeping track of eliminatedState => stateKept
      val stateMap = mutable.HashMap[Int, Int]()

      val transStateMap = flatTrans.groupBy(_._1).mapValues(l => l map (_._2))
      println("transStateMap:\n" + transStateMap)
      /*
    The above map is still rough, as in the values can contain states that are final, nonfinal, noninitial, initial
    We have to split them in group of states:
    - plain : neither final nor initial
    - fi : final and initial
    - f : final
    - i : initial
     */
      var plainTSM = transStateMap.mapValues(_.filter(x => !aut.initialStates.contains(x) && !aut.finalStates.contains(x)))
      var fiTSM = transStateMap.mapValues(_.filter(x => aut.initialStates.contains(x) && aut.finalStates.contains(x)))
      var fTSM = transStateMap.mapValues(_.filter(x => !aut.initialStates.contains(x) && aut.finalStates.contains(x)))
      var iTSM = transStateMap.mapValues(_.filter(x => aut.initialStates.contains(x) && !aut.finalStates.contains(x)))

      plainTSM = plainTSM.filter(_._2.nonEmpty)
      fiTSM = fiTSM.filter(_._2.nonEmpty)
      fTSM = fTSM.filter(_._2.nonEmpty)
      iTSM = iTSM.filter(_._2.nonEmpty)

      println("plainTSM:\n" + plainTSM)
      println("fiTSM:\n" + fiTSM)
      println("fTSM:\n" + fTSM)
      println("iTSM:\n" + iTSM)


      for ((_, sts) <- plainTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- fiTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- fTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      for ((_, sts) <- iTSM) {
        val statesIt = sts.iterator
        // This is the only states that is kept, there is at least one
        val uniqueSt = statesIt.next()
        // Build the map of states that has to be eliminated as key and the replacement as value
        while (statesIt.hasNext) stateMap += ((statesIt.next(), uniqueSt))
      }

      /* Now in the keyset of StateMap contains all and only states that has to be removed.
    The removal strategy is the following:
    (1) filter the transitions map with states to be removed;
    (2) scan such reduced transitions and map the arrival states with stateMap
     */
      val toBeRemoved = stateMap.keySet.toSet
      println("Removed map:\n" + stateMap)
      println("To be removed:\n" + toBeRemoved)
      // All other states have to be mapped to themsleves!
      for (s <- aut.states.toSet--toBeRemoved) stateMap += ((s, s))
      val reducedTrans = aut.transitions.filterNot(x => toBeRemoved.contains(x._1))
      println("Reduced trans:\n" + reducedTrans)
      val newTrans = reducedTrans.mapValues(_.map(x => StepTransition(x.label, x.step, x.targets.map(stateMap))))

      val newTransConverted = newTrans.map{ case (st, ts) =>
        val newTS = ts.map(x => StepTransition(x.label, x.step, x.targets.map(x => {if (x==SELF) st else x}) ))
        (st, newTS)
      }

      val newAut = AFA2(aut.initialStates, aut.finalStates, newTrans.toMap)

      newAut.restrictToReachableStates
    }


    var oldAut = this
    var newAut = minimizeStatesStep(oldAut)
    while (newAut.states.size != oldAut.states.size) {
      oldAut = newAut
      newAut = minimizeStatesStep(oldAut)
    }
    newAut

  }

  def optimizeUntilFixpoint() : AFA2 = {
    var oldAut = this.restrictToReachableStates
    var newAut = oldAut.dominatedStateCheck().partitionRefinement()

    while (newAut.states.size != oldAut.states.size) {
      oldAut = newAut
      newAut = oldAut.dominatedStateCheck().partitionRefinement()
    }

    newAut
  }

  // TODO: Finish this
  private  def dominatedStateCheck() : AFA2 = {
    // label, direction and now active states
    type Move = (Int, Step, Seq[Int])
    // a sequence of moves, the set of active states
    // of the final move is currently active
    type Path = Seq[Seq[Move]]

    def getActiveStates(path: Path): Seq[Int] = {
      path.last.flatMap(move => move._3)
    }

    def getAllPaths(start: Int, n: Int): Seq[Path] = {
      def getPossibleMovesFromActiveState(state: Int): Seq[Move] = {
        var moves = Seq[Move]()
        for (element <- transitions(state)) {
          moves :+ (element.label, element.step, element.targets)
        }
        moves
      }

      // TODO: Check if the cartesian product is calculated correctly
      def getMoveCombinations(activeStates: Seq[Int]): Seq[Seq[Move]] = {
        // no active states -> no combinations
        if (activeStates.isEmpty) {
          return Seq()
        }

        // each possible move of the first active state starts one combination
        var combinations = Seq[Seq[Move]]()
        for (move <- getPossibleMovesFromActiveState(activeStates.head)) {
          combinations = combinations :+ Seq(move)
        }

        // extend every combination with every possible move
        // of the remaining active states
        for (i <- 1 until activeStates.size) {
          val state = activeStates(i)
          var newCombinations = Seq[Seq[Move]]()

          for (combination <- combinations) {
            for (move <- getPossibleMovesFromActiveState(state)) {
              newCombinations = newCombinations :+ (combination :+ move)
            }
          }

          combinations = newCombinations
        }

        combinations
      }

      // each possible initial move forms one path with one step
      var paths = Seq[Path]()
      for (move <- getPossibleMovesFromActiveState(start)) {
        paths = paths :+ Seq(Seq(move))
      }

      // extend the paths by at most n additional steps.
      for (_ <- 0 until n) {
        var newPaths = Seq[Path]()

        for (path <- paths) {
          val activeStates = getActiveStates(path)
          for (nextStep <- getMoveCombinations(activeStates)) {
            newPaths = newPaths :+ (path :+ nextStep)
          }
        }

        paths = newPaths
      }

      paths
    }

    def sameIncomingBehavior(a: Int, b: Int): Boolean = {

    }

    // checks if the transition behavior of a covers that of b
    // returns all paths that are redundant
    def covers(a: Int, b: Int, n: Int): Path = {
      def pathIsSubset(pathB: Path, pathA: Path): Boolean = {
        // every step of B must be a subset of the corresponding step of A.
        for (i <- pathB.indices) {
          val stepB = pathB(i).toSet
          val stepA = pathA(i).toSet

          if (!stepB.subsetOf(stepA)) {
            false
          }
        }


        // both paths must reach the same active states.
        getActiveStates(pathB).toSet == getActiveStates(pathA).toSet
      }

      // Check all path lengths from 1 to n.
      for (length <- 1 to n) {
        val pathsFromA = getAllPaths(a, length)
        val pathsFromB = getAllPaths(b, length)

        // Every path from B must be covered by a path from A.
        for (pathB <- pathsFromB) {
          var matchingPathFound = false
          for (pathA <- pathsFromA) {
            if (pathIsSubset(pathB, pathA)) {
              matchingPathFound = true
            }
          }

          if (!matchingPathFound) {
            return false
          }
        }
      }
    }

    def domiates(a: Int, b: Int): Boolean = {
      true
    }

    def merge(a: Int, b: Int) = {

    }

    for (a <- states) {
      for (b <- states if a != b) {
        if(domiates(a, b))
        {
            merge(a, b)
        }
      }
    }

    this
  }

  /*
   * Reduces the size of the automaton using a partition refinement procedure,
   * that is similar to the hopcroft algorithm for DFAs.
   * We sort states into equivalence classes based on their outgoing transition behavior.
   * A formalization and a correctness proof can be found in chapter 5.2 of the bachelor's thesis
   * "Optimized Methods for Translating Two-Way
   * Alternating Automata to One-Way
   * Non-Deterministic Automata" by Henrik Oback, 2442473
   * available at the "University Library of Regensburg".
   */
  private def partitionRefinement() : AFA2 = {
    // label / left or right / target
    type TransitionSignature = (Int, Step, Set[Int])
    // last partition and set of all transition signatures
    type Signature = (Int, Set[TransitionSignature])

    // map every state to its partition number
    var partitions = mutable.HashMap[Int, Int]()

    // initial partition final/non-final states
    for (state <- finalStates) {
      partitions += ((state, 0))
    }
    for (state <- states) {
      if (!finalStates.contains(state)) {
        partitions += ((state, 1))
      }
    }

    def getSignature(state: Int) : Signature = {
      val outgoingTransitions = transitions.getOrElse(state, Seq())

      // iterate the outgoing transitions and yield their transition signatures
      val transitionSignatures = for (transition <- outgoingTransitions) yield {
        var targetPartitions = Set[Int]()
        for (target <- transition.targets) {
          targetPartitions += partitions(target)
        }

        // consumed symbol / right or left step / reached partitions
        // there can be multible partitions reached by one transition due to universal branching
        (transition.label, transition.step, targetPartitions)
      }

      // convert to set since duplicate entries should not affect the signature
      (partitions(state), transitionSignatures.toSet)
    }

    // iterate until the last refinement is the same as the current one
    var changed = true
    while(changed) {

      // get the signature of every state
      var allSignatures = mutable.HashMap[Int, Signature]()
      for (state <- states) {
        allSignatures += ((state, getSignature(state)))
      }

      // assign a partition number to every unique signature
      val signatureToPartition = mutable.HashMap[Signature, Int]()
      var nextPartition = 0
      for ((_, signature) <- allSignatures) {
        if (!signatureToPartition.contains(signature)) {
          signatureToPartition += ((signature, nextPartition))
          nextPartition += 1
        }
      }

      // map every state to the partition number of its signature
      val newPartitions = mutable.HashMap[Int, Int]()
      for ((state, signature) <- allSignatures) {
        newPartitions += ((state, signatureToPartition(signature)))
      }

      if (newPartitions == partitions) {
        changed = false
      } else {
        partitions = newPartitions
      }
    }

    // finally map the states to their partition
    val newInitialStates = initialStates.map(partitions).distinct
    val newFinalStates = finalStates.map(partitions).distinct
    val newTransitions = mutable.HashMap[Int, Seq[StepTransition]]()

    for ((source, outgoing) <- transitions) {
      val newSource = partitions(source)

      val mappedTransitions = for (transition <- outgoing) yield {
        StepTransition(
          transition.label,
          transition.step,
          transition.targets.map(partitions)
        )
      }

      // add mapped transitions to the ones that were already mapped
      val buffer = newTransitions.getOrElse(newSource, Seq())
      newTransitions(newSource) = (buffer ++ mappedTransitions).distinct
    }

    // return the reduced automaton
    AFA2(newInitialStates, newFinalStates, newTransitions.toMap).restrictToReachableStates
  }

  /*
   * Eliminates non-forward reachable and non-backward reachable states.
   */
  def restrictToReachableStates : AFA2 =
    if (reachableStates.size == states.size) {
      this
    } else {
      val newInitialPre =
        initialStates filter reachableStates
      val newInitial =
        if (newInitialPre.isEmpty)
          initialStates take 1
        else
          newInitialPre

      val newFinal =
        finalStates filter reachableStates
      val newTransitions =
        for ((source, ts) <- transitions;
             if (reachableStates contains source)) yield {
          val newTS =
            for (t@StepTransition(_, _, targets) <- ts;
                 if targets forall reachableStates)
            yield t
          source -> newTS
        }

      AFA2(newInitial, newFinal, newTransitions)
    }

  // Different categories of states:
  //
  // ir: initial,                       outgoing transitions go right
  // ll: incoming transitions go left,  outgoing transitions go left
  // lr: incoming transitions go left,  outgoing transitions go right
  // rl: incoming transitions go right, outgoing transitions go left
  // rr: incoming transitions go right, outgoing transitions go right
  // rf: incoming transitions go right, final

  lazy val (irStates, llStates, lrStates, rlStates, rrStates, rfStates) = {
    val leftIn, rightIn, leftOut, rightOut = new MHashSet[Int]

    for ((source, ts)                     <- transitions.iterator;
         StepTransition(_, step, targets) <- ts.iterator;
         target                           <- targets.iterator) {
      step match {
        case Left  => {
          leftOut  += source
          leftIn   += target
        }
        case Right => {
          rightOut += source
          rightIn  += target
        }
      }
    }

    val onlyLeftIn   = leftIn -- rightIn
    val onlyRightIn  = rightIn -- leftIn
    val onlyLeftOut  = leftOut -- rightOut
    val onlyRightOut = rightOut -- leftOut

    val anyIn        = leftIn ++ rightIn
    val anyOut       = leftOut ++ rightOut

    (initialStates.toSet & onlyRightOut.toSet -- anyIn -- finalStates,
      onlyLeftIn.toSet  & onlyLeftOut.toSet -- initialStates -- finalStates,
      onlyLeftIn.toSet  & onlyRightOut.toSet -- initialStates -- finalStates,
      onlyRightIn.toSet & onlyLeftOut.toSet -- initialStates -- finalStates,
      onlyRightIn.toSet & onlyRightOut.toSet -- initialStates -- finalStates,
      finalStates.toSet & onlyRightIn.toSet -- anyOut -- initialStates)
  }

  lazy val letters =
    (for ((source, ts)            <- transitions.iterator;
          StepTransition(l, _, _) <- ts.iterator)
    yield l).toSet.toIndexedSeq.sorted

}
