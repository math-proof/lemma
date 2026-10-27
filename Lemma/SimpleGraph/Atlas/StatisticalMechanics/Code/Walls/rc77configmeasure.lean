import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part4
open Finset StatMech StatMech.Walls


/--
[rc77_downUp_increases_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean)
-/
@[path]
private lemma rc77_downUp_increases_fin2_eq :
-- imply
  (rc75_disjOccF rc77_wA rc77_wB).card = 0 ∧ (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).card = 1 := by
-- proof
  apply StatMech.Walls.rc77_downUp_increases_fin2

/--
[rc77_downUp_count_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean)
-/
@[path]
private lemma rc77_downUp_count_fin2_eq :
-- imply
  rc77_downUpIncreases = 56 ∧ rc77_downUpDecreases = 0 := by
-- proof
  apply StatMech.Walls.rc77_downUp_count_fin2

/--
[rc77_all_dirs_fail_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean)
-/
@[path]
private lemma rc77_all_dirs_fail_fin2_eq :
-- imply
  rc77_incCount rc77_downEvt rc77_upEvt = 56 ∧ rc77_decCount rc77_downEvt rc77_upEvt = 0 ∧ rc77_incCount rc77_upEvt rc77_downEvt = 56 ∧ rc77_decCount rc77_upEvt rc77_downEvt = 0 ∧ rc77_incCount rc77_downEvt rc77_downEvt = 48 ∧ rc77_decCount rc77_downEvt rc77_downEvt = 8 ∧ rc77_incCount rc77_upEvt rc77_upEvt = 48 ∧ rc77_decCount rc77_upEvt rc77_upEvt = 8 := by
-- proof
  apply StatMech.Walls.rc77_all_dirs_fail_fin2

/--
[rc77_fixpoint_wall_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean)
-/
@[path]
private lemma rc77_fixpoint_wall_fin2_eq :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 2)), rc77_isDownEvt A = true → rc77_isUpEvt B = true → 2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card := by
-- proof
  apply StatMech.Walls.rc77_fixpoint_wall_fin2

/--
[rc77_witness_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean)
-/
@[path]
private lemma rc77_witness_nonvacuous_eq :
-- imply
  (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).Nonempty := by
-- proof
  apply StatMech.Walls.rc77_witness_nonvacuous

/--
[rc77_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean)
-/
@[path]
private lemma rc77_reimerWprobCore_of_boxUnionBound_eq
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc77_reimerWprobCore_of_boxUnionBound h

/--
[rc77_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean)
-/
@[path]
private lemma rc77_status_eq :
-- imply
  ((rc75_disjOccF rc77_wA rc77_wB).card = 0 ∧ (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).card = 1) ∧ (rc77_downUpIncreases = 56 ∧ rc77_downUpDecreases = 0) ∧ (rc77_incCount rc77_downEvt rc77_upEvt = 56 ∧ rc77_incCount rc77_upEvt rc77_downEvt = 56 ∧ rc77_incCount rc77_downEvt rc77_downEvt = 48 ∧ rc77_incCount rc77_upEvt rc77_upEvt = 48) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), rc77_isDownEvt A = true → rc77_isUpEvt B = true → 2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc77_status


-- created on 2026-10-23
