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
    var newAut = oldAut.partitionRefinement().dominatedStateCheck()

    while (newAut.states.size != oldAut.states.size) {
      oldAut = newAut
      newAut = oldAut.partitionRefinement().dominatedStateCheck()
    }

    newAut
  }

  def getRestAutomaton(q: Int): AFA2 = {
    AFA2(
      Seq(q),
      finalStates,
      transitions
    ).restrictToReachableStates
  }

  def merge(q: Int, p: Int): AFA2 = {
    // replace q with p in the initial states
    val newInitialStates = initialStates
      .map(state => if (state == q) p else state)
      .distinct

    // replace a with b in the final states
    val newFinalStates = finalStates
      .map(state => if (state == q) p else state)
      .distinct

    val newTransitions = mutable.HashMap[Int, Seq[StepTransition]]()

    for ((source, outgoingTransitions) <- transitions) {
      // remove q as a source state.
      if (source != q) {
        var mappedTransitions = Seq[StepTransition]()

        for (transition <- outgoingTransitions) {
          // replace q with p in every target list.
          val newTargets = transition.targets
            .map(target => if (target == q) p else target)
            .distinct

          mappedTransitions = mappedTransitions :+
            StepTransition(
              transition.label,
              transition.step,
              newTargets
            )
        }

        newTransitions += ((source, mappedTransitions.distinct))
      }
    }

    AFA2(
      newInitialStates,
      newFinalStates,
      newTransitions.toMap
    ).restrictToReachableStates
  }

  private  def dominatedStateCheck() : AFA2 = {

    def sameIncomingBehavior(q: Int, p: Int, automaton: AFA2): Boolean = {
      // source state, label, direction, targets
      type IncomingTransition = (Int, Int, Step, Seq[Int])

      var incomingQ = Set[IncomingTransition]()
      var incomingP = Set[IncomingTransition]()

      // collect all transitions that lead to q or p
      for ((source, outgoingTransitions) <- automaton.transitions) {
        for (transition <- outgoingTransitions) {

          if (transition.targets.contains(q)) {
            incomingQ += ((
              source,
              transition.label,
              transition.step,
              transition.targets
            ))
          }

          if (transition.targets.contains(p)) {
            incomingP += ((
              source,
              transition.label,
              transition.step,
              transition.targets
            ))
          }
        }
      }

      // use a fresh placeholder state
      val r = -1

      var normalizedQ = Set[IncomingTransition]()
      var normalizedP = Set[IncomingTransition]()

      // replace q with r in all transitions leading to q
      for ((source, label, step, targets) <- incomingQ) {
        val newTargets = targets.map(target => if (target == q) r else target)
        normalizedQ += ((source, label, step, newTargets))
      }

      // replace p with r in all transitions leading to p
      for ((source, label, step, targets) <- incomingP) {
        val newTargets = targets.map(target => if (target == p) r else target)
        normalizedP += ((source, label, step, newTargets))
      }

      normalizedQ == normalizedP
    }

    def subsetLanguage(q: Int, p: Int, automaton: AFA2): Boolean = {
      // we only check rest automata with a fixed size!
      // if they are too big just say false
      val limit = 6

      val automatonQ = automaton.getRestAutomaton(q)
      if(automatonQ.states.size > limit) {
        return false
      }
      val automatonP = automaton.getRestAutomaton(p)
      if(automatonP.states.size > limit) {
        return false
      }

      val nfaQ = NFATranslator(AFA2StateDuplicator(automatonQ), null)
      val nfaP = NFATranslator(AFA2StateDuplicator(automatonP), null)

      // q is a subset of p
      val aMinusB = nfaQ & !nfaP
      aMinusB.isEmpty
    }

    def outgoingBehaviorSubset(q: Int, p: Int, automaton: AFA2): Boolean = {
      val transitionsQ = automaton.transitions.getOrElse(q, Seq()).toSet
      val transitionsP = automaton.transitions.getOrElse(p, Seq()).toSet

      transitionsQ.subsetOf(transitionsP)
    }

    var newAutomaton = AFA2(initialStates, finalStates, transitions)
    var deletion = true

    while (deletion) {
      deletion = false

      for (q <- newAutomaton.states if !deletion) {
        for (p <- newAutomaton.states if !deletion && q != p &&
          !newAutomaton.initialStates.contains(q) &&
          !newAutomaton.finalStates.contains(q) &&
          !newAutomaton.initialStates.contains(p) &&
          !newAutomaton.finalStates.contains(p)) {

          val same_incoming_behavior = sameIncomingBehavior(q, p, newAutomaton)
          if(same_incoming_behavior && outgoingBehaviorSubset(q, p, newAutomaton)) {
            newAutomaton = newAutomaton.merge(q, p)
            deletion = true
          }

          if(!deletion) {
            val q_subset_p = subsetLanguage(q, p, newAutomaton)
            if(q_subset_p && same_incoming_behavior) {
              newAutomaton = newAutomaton.merge(q, p)
              deletion = true
            }

            if(!deletion && q_subset_p) {
              val p_subset_q = subsetLanguage(p, q, newAutomaton)
              if(p_subset_q) {
                newAutomaton = newAutomaton.merge(q, p)
                deletion = true
              }
            }
          }
        }
      }
    }

    newAutomaton
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
