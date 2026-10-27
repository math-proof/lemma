import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncationLimit.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FK


/--
[continuous_pottsClusterSumSpin_wiredTruncationEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncationLimit.lean)
-/
@[path]
private lemma continuous_pottsClusterSumSpin_wiredTruncationEdge_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {n : Nat} :
-- imply
  Continuous (fun input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) => pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n input.1) input.2) := by
-- proof
  apply StatMech.FK.continuous_pottsClusterSumSpin_wiredTruncationEdge boundaryColor n

/--
[tendsto_pottsClusterSumSpin_wiredTruncationEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncationLimit.lean)
-/
@[path]
private lemma tendsto_pottsClusterSumSpin_wiredTruncationEdge_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
-- given
  (hd : 2 <= d)
  (label : Site d -> Fin q) :
-- imply
  Tendsto (fun n => pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega) label) atTop (nhds (pottsClusterSumSpin boundaryColor omega label)) := by
-- proof
  apply StatMech.FK.tendsto_pottsClusterSumSpin_wiredTruncationEdge hd boundaryColor omega label

/--
[measurable_pottsClusterSumSpin_wiredTruncationEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncationLimit.lean)
-/
@[path]
private lemma measurable_pottsClusterSumSpin_wiredTruncationEdge_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {n : Nat} :
-- imply
  Measurable (fun input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) => pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n input.1) input.2) := by
-- proof
  apply StatMech.FK.measurable_pottsClusterSumSpin_wiredTruncationEdge boundaryColor n

/--
[tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncationLimit.lean)
-/
@[path]
private lemma tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure_of_tendsto_eq
  {d q : Nat}
  [NeZero q]
  {L : Filter I}
  {boundaryColor : Fin q}
  {edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {n : Nat}
-- given
  (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
  (hedge : Tendsto edgeSeq L (nhds edgeLimit)) :
-- imply
  Tendsto (fun i => wiredTruncatedPottsClusterSumSpinProbabilityMeasure boundaryColor (edgeSeq i) n) L (nhds (wiredTruncatedPottsClusterSumSpinProbabilityMeasure boundaryColor edgeLimit n)) := by
-- proof
  apply StatMech.FK.tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure_of_tendsto boundaryColor edgeSeq edgeLimit n hedge

/--
[tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncationLimit.lean)
-/
@[path]
private lemma tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 2 <= d) :
-- imply
  Tendsto (wiredTruncatedPottsClusterSumSpinProbabilityMeasure boundaryColor edgeMeasure) atTop (nhds ((pottsClusterSumJointProbabilityMeasure boundaryColor edgeMeasure).map continuous_fst.measurable.aemeasurable)) := by
-- proof
  apply StatMech.FK.tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure hd boundaryColor edgeMeasure


-- created on 2026-10-23
