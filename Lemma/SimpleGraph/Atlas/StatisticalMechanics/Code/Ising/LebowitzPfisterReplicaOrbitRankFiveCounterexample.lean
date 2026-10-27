import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample
open Finset StatMech StatMech.Ising StatMech.Ising.LPRankFiveCounterexample


/--
[offdiag_sources_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma offdiag_sources_iff_eq :
-- imply
  ∀ o K, sources o K = offdiag ↔ (o = orientationLeft ∧ K = Finset.univ) ∨ (o = orientationRight ∧ K = Finset.univ) := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.offdiag_sources_iff

/--
[no_seamI_sources_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma no_seamI_sources_left_eq :
-- imply
  ∀ K : Finset LPRankFiveCounterSlot, sources orientationLeft K ≠ seamI := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.no_seamI_sources_left

/--
[no_seamI_sources_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma no_seamI_sources_right_eq :
-- imply
  ∀ K : Finset LPRankFiveCounterSlot, sources orientationRight K ≠ seamI := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.no_seamI_sources_right

/--
[no_seamJ_sources_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma no_seamJ_sources_left_eq :
-- imply
  ∀ K : Finset LPRankFiveCounterSlot, sources orientationLeft K ≠ seamJ := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.no_seamJ_sources_left

/--
[no_seamJ_sources_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma no_seamJ_sources_right_eq :
-- imply
  ∀ K : Finset LPRankFiveCounterSlot, sources orientationRight K ≠ seamJ := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.no_seamJ_sources_right

/--
[left_boundary_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma left_boundary_symmDiff_eq :
-- imply
  seamI ∆ (seamJ ∪ ghosts) = offdiag := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.left_boundary_symmDiff

/--
[right_boundary_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma right_boundary_symmDiff_eq :
-- imply
  seamJ ∆ (seamI ∪ ghosts) = offdiag := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.right_boundary_symmDiff

/--
[colorClass_disjoint_zero_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma colorClass_disjoint_zero_two_eq
  {c : LPRankFiveCounterColoring} :
-- imply
  Disjoint (colorClass c 0) (colorClass c 2) := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.colorClass_disjoint_zero_two c

/--
[not_left_target_boundaryPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma not_left_target_boundaryPattern_eq
  (o)
  (c) :
-- imply
  ¬ boundaryPattern o seamI (seamJ ∪ ghosts) c := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.not_left_target_boundaryPattern

/--
[not_right_target_boundaryPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma not_right_target_boundaryPattern_eq
  (o)
  (c) :
-- imply
  ¬ boundaryPattern o seamJ (seamI ∪ ghosts) c := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.not_right_target_boundaryPattern

/--
[source_pattern_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma source_pattern_left_eq :
-- imply
  pattern orientationLeft ∅ offdiag saturatedColoring := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.source_pattern_left

/--
[source_pattern_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma source_pattern_right_eq :
-- imply
  pattern orientationRight ∅ offdiag saturatedColoring := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.source_pattern_right

/--
[not_left_target_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma not_left_target_pattern_eq
  (o)
  (c) :
-- imply
  ¬ pattern o seamI (seamJ ∪ ghosts) c := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.not_left_target_pattern

/--
[not_right_target_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma not_right_target_pattern_eq
  (o)
  (c) :
-- imply
  ¬ pattern o seamJ (seamI ∪ ghosts) c := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.not_right_target_pattern

/--
[sourceState_left_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma sourceState_left_mem_eq :
-- imply
  (orientationLeft, saturatedColoring) ∈ sourceStates := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.sourceState_left_mem

/--
[sourceState_right_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma sourceState_right_mem_eq :
-- imply
  (orientationRight, saturatedColoring) ∈ sourceStates := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.sourceState_right_mem

/--
[sourceStates_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma sourceStates_nonempty_eq :
-- imply
  sourceStates.Nonempty := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.sourceStates_nonempty

/--
[sourceStates_card_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma sourceStates_card_ge_two_eq :
-- imply
  2 <= sourceStates.card := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.sourceStates_card_ge_two

/--
[leftTargetStates_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma leftTargetStates_eq_empty_eq :
-- imply
  leftTargetStates = ∅ := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.leftTargetStates_eq_empty

/--
[rightTargetStates_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma rightTargetStates_eq_empty_eq :
-- imply
  rightTargetStates = ∅ := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.rightTargetStates_eq_empty

/--
[leftTargetStates_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma leftTargetStates_card_eq :
-- imply
  leftTargetStates.card = 0 := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.leftTargetStates_card

/--
[rightTargetStates_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma rightTargetStates_card_eq :
-- imply
  rightTargetStates.card = 0 := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.rightTargetStates_card

/--
[not_source_card_le_target_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean)
-/
@[path]
private lemma not_source_card_le_target_card_eq :
-- imply
  ¬ sourceStates.card ≤ leftTargetStates.card + rightTargetStates.card := by
-- proof
  apply StatMech.Ising.LPRankFiveCounterexample.not_source_card_le_target_card


-- created on 2026-10-23
