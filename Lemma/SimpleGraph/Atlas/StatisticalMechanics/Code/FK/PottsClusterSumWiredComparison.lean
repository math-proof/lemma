import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredComparison.Part4
open Filter MeasureTheory Set Topology StatMech StatMech.FK


/--
[abs_map_real_sub_map_real_le_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma abs_map_real_sub_map_real_le_disagreement_eq
  [MeasurableSpace Omega]
  [MeasurableSpace Xi]
  [MeasurableEq Xi]
  {mu : Measure Omega}
  [IsFiniteMeasure mu]
  {A : Set Xi}
-- given
  (f g : Omega -> Xi)
  (hf : Measurable f)
  (hg : Measurable g)
  (hA : MeasurableSet A) :
-- imply
  abs ((Measure.map f mu).real A - (Measure.map g mu).real A) ≤ mu.real {z | f z ≠ g z} := by
-- proof
  apply StatMech.FK.abs_map_real_sub_map_real_le_disagreement mu f g hf hg A hA

/--
[abs_map_real_sub_map_real_le_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma abs_map_real_sub_map_real_le_error_eq
  [MeasurableSpace Omega]
  [MeasurableSpace Xi]
  {mu : Measure Omega}
  [IsFiniteMeasure mu]
  {A : Set Xi}
  {D : Set Omega}
-- given
  (f g : Omega -> Xi)
  (hf : Measurable f)
  (hg : Measurable g)
  (hA : MeasurableSet A)
  (hagree : ∀ z, z ∉ D -> (f z ∈ A ↔ g z ∈ A)) :
-- imply
  abs ((Measure.map f mu).real A - (Measure.map g mu).real A) ≤ mu.real D := by
-- proof
  apply StatMech.FK.abs_map_real_sub_map_real_le_error mu f g hf hg A hA D hagree

/--
[ProbabilityMeasure.ext_of_pottsSpinCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma ext_of_pottsSpinCylinder_eq
  {d q : Nat}
  {mu nu : ProbabilityMeasure (PottsConfig d q)}
-- given
  (h : ∀ (sites : Finset (Site d)) (colors : Set (∀ _x : sites, Fin q)), mu (cylinder (α := fun _ : Site d => Fin q) sites colors) = nu (cylinder (α := fun _ : Site d => Fin q) sites colors)) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FK.ProbabilityMeasure.ext_of_pottsSpinCylinder mu nu h

/--
[measurableSet_wiredTruncationErrorEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma measurableSet_wiredTruncationErrorEvent_eq
  {d R : Nat}
  {x : Site d} :
-- imply
  MeasurableSet (wiredTruncationErrorEvent d R x) := by
-- proof
  apply StatMech.FK.measurableSet_wiredTruncationErrorEvent d R x

/--
[tendsto_wiredTruncationErrorEvent_real_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma tendsto_wiredTruncationErrorEvent_real_zero_eq
  {d : Nat}
  {x : Site d}
  {edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))} :
-- imply
  Tendsto (fun R => (edgeMeasure : Measure _).real (wiredTruncationErrorEvent d R x)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.tendsto_wiredTruncationErrorEvent_real_zero x edgeMeasure

/--
[tendsto_wiredTruncationErrorEvent_real_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma tendsto_wiredTruncationErrorEvent_real_of_tendsto_eq
  {d R : Nat}
  {L : Filter I}
  {x : Site d}
  {edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 2 ≤ d)
  (hR : 1 ≤ R)
  (hx : x ∈ box d R)
  (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
  (hedge : Tendsto edgeSeq L (nhds edgeLimit))
  (hinfinite : Tendsto (fun i => (edgeSeq i : Measure _).real (clusterInfiniteEvent d x)) L (nhds ((edgeLimit : Measure _).real (clusterInfiniteEvent d x)))) :
-- imply
  Tendsto (fun i => (edgeSeq i : Measure _).real (wiredTruncationErrorEvent d R x)) L (nhds ((edgeLimit : Measure _).real (wiredTruncationErrorEvent d R x))) := by
-- proof
  apply StatMech.FK.tendsto_wiredTruncationErrorEvent_real_of_tendsto hd hR x hx edgeSeq edgeLimit hedge hinfinite

/--
[measurableSet_pottsSpinTruncationDisagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma measurableSet_pottsSpinTruncationDisagreement_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {R : Nat}
  {sites : Finset (Site d)} :
-- imply
  MeasurableSet (pottsSpinTruncationDisagreement boundaryColor R sites) := by
-- proof
  apply StatMech.FK.measurableSet_pottsSpinTruncationDisagreement boundaryColor R sites

/--
[pottsSpinCylinder_membership_iff_of_not_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma pottsSpinCylinder_membership_iff_of_not_disagreement_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {R : Nat}
  {sites : Finset (Site d)}
-- given
  (colors : Set (∀ _x : sites, Fin q))
  (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
  (hinput : input ∉ pottsSpinTruncationDisagreement boundaryColor R sites) :
-- imply
  pottsClusterSumSpin boundaryColor input.1 input.2 ∈ cylinder (α := fun _ : Site d => Fin q) sites colors ↔ pottsClusterSumSpin boundaryColor (wiredTruncationEdge d R input.1) input.2 ∈ cylinder (α := fun _ : Site d => Fin q) sites colors := by
-- proof
  apply StatMech.FK.pottsSpinCylinder_membership_iff_of_not_disagreement boundaryColor R sites colors input hinput

/--
[pottsSpinTruncationDisagreement_real_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma pottsSpinTruncationDisagreement_real_le_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {R : Nat}
  {sites : Finset (Site d)}
  {edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 2 ≤ d)
  (hR : 1 ≤ R)
  (hsites : ∀ x ∈ sites, x ∈ box d R) :
-- imply
  ((edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)).real (pottsSpinTruncationDisagreement boundaryColor R sites) ≤ ∑ x ∈ sites, (edgeMeasure : Measure _).real (wiredTruncationErrorEvent d R x) := by
-- proof
  apply StatMech.FK.pottsSpinTruncationDisagreement_real_le hd boundaryColor R hR sites hsites edgeMeasure

/--
[pottsClusterSumSpinProbabilityMeasure_eq_joint_map_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma pottsClusterSumSpinProbabilityMeasure_eq_joint_map_fst_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))} :
-- imply
  pottsClusterSumSpinProbabilityMeasure boundaryColor edgeMeasure = (pottsClusterSumJointProbabilityMeasure boundaryColor edgeMeasure).map continuous_fst.measurable.aemeasurable := by
-- proof
  apply StatMech.FK.pottsClusterSumSpinProbabilityMeasure_eq_joint_map_fst boundaryColor edgeMeasure

/--
[abs_clusterSumSpin_sub_truncated_real_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean)
-/
@[path]
private lemma abs_clusterSumSpin_sub_truncated_real_le_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {R : Nat}
  {sites : Finset (Site d)}
  {edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 2 ≤ d)
  (hR : 1 ≤ R)
  (colors : Set (∀ _x : sites, Fin q))
  (hsites : ∀ x ∈ sites, x ∈ box d R) :
-- imply
  abs ((pottsClusterSumSpinProbabilityMeasure boundaryColor edgeMeasure : Measure _).real (cylinder (α := fun _ : Site d => Fin q) sites colors) - (wiredTruncatedPottsClusterSumSpinProbabilityMeasure boundaryColor edgeMeasure R : Measure _).real (cylinder (α := fun _ : Site d => Fin q) sites colors)) ≤ ∑ x ∈ sites, (edgeMeasure : Measure _).real (wiredTruncationErrorEvent d R x) := by
-- proof
  apply StatMech.FK.abs_clusterSumSpin_sub_truncated_real_le hd boundaryColor R hR sites colors hsites edgeMeasure


-- created on 2026-10-23
