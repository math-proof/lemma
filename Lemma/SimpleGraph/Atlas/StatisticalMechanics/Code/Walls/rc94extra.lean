import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc94extra.Part3
open Finset StatMech StatMech.Walls


/--
[rc94_compl_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_compl_involutive_eq
  [Fintype ι]
  [DecidableEq ι]
  {w : ConfigSpace ι} :
-- imply
  rc80_compl (rc80_compl w) = w := by
-- proof
  apply StatMech.Walls.rc94_compl_involutive w

/--
[rc94_compl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_compl_injective_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  Function.Injective (rc80_compl : ConfigSpace ι → ConfigSpace ι) := by
-- proof
  apply StatMech.Walls.rc94_compl_injective

/--
[rc94_reflInterG_image_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_reflInterG_image_compl_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)} :
-- imply
  rc80_reflInterG A B = (rc80_reflInterG B A).image rc80_compl := by
-- proof
  apply StatMech.Walls.rc94_reflInterG_image_compl A B

/--
[rc94_reflInterG_card_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_reflInterG_card_symm_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_reflInterG A B).card = (rc80_reflInterG B A).card := by
-- proof
  apply StatMech.Walls.rc94_reflInterG_card_symm A B

/--
[rc94_inter_subset_reflInterG_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_inter_subset_reflInterG_symm_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc94_InterCoverA A B) :
-- imply
  A ∩ B ⊆ rc80_reflInterG B A := by
-- proof
  apply StatMech.Walls.rc94_inter_subset_reflInterG_symm A B h

/--
[rc94_wall_interCoverA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_wall_interCoverA_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc94_InterCoverA A B) :
-- imply
  (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
-- proof
  apply StatMech.Walls.rc94_wall_interCoverA A B h

/--
[rc94_interCoverA_of_complClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_interCoverA_of_complClosed_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc90_ComplClosed A) :
-- imply
  rc94_InterCoverA A B := by
-- proof
  apply StatMech.Walls.rc94_interCoverA_of_complClosed A B h

/--
[rc94_A3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc94_A3 := by
-- proof
  apply StatMech.Walls.rc94_A3_not_upper

/--
[rc94_A3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc94_A3 := by
-- proof
  apply StatMech.Walls.rc94_A3_not_lower

/--
[rc94_B3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_B3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc94_B3 := by
-- proof
  apply StatMech.Walls.rc94_B3_not_upper

/--
[rc94_B3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_B3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc94_B3 := by
-- proof
  apply StatMech.Walls.rc94_B3_not_lower

/--
[rc94_A3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc94_A3.card = 3 := by
-- proof
  apply StatMech.Walls.rc94_A3_card

/--
[rc94_B3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_B3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc94_B3.card = 5 := by
-- proof
  apply StatMech.Walls.rc94_B3_card

/--
[rc94_A3_B3_inter_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_B3_inter_nonempty_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc94_A3 ∩ rc94_B3).Nonempty := by
-- proof
  apply StatMech.Walls.rc94_A3_B3_inter_nonempty

/--
[rc94_A3_B3_interCoverA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_B3_interCoverA_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc94_InterCoverA rc94_A3 rc94_B3 := by
-- proof
  apply StatMech.Walls.rc94_A3_B3_interCoverA

/--
[rc94_A3_B3_not_rc93](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_B3_not_rc93_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc93_InterCover rc94_A3 rc94_B3 := by
-- proof
  apply StatMech.Walls.rc94_A3_B3_not_rc93

/--
[rc94_A3_B3_inter_not_subset_reflInterG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_B3_inter_not_subset_reflInterG_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ (rc94_A3 ∩ rc94_B3 ⊆ rc80_reflInterG rc94_A3 rc94_B3) := by
-- proof
  apply StatMech.Walls.rc94_A3_B3_inter_not_subset_reflInterG

/--
[rc94_A3_B3_not_reflCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_B3_not_reflCover_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc90_ReflCover rc94_A3 rc94_B3 := by
-- proof
  apply StatMech.Walls.rc94_A3_B3_not_reflCover

/--
[rc94_A3_B3_disjOcc_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_A3_B3_disjOcc_nonempty_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG rc94_A3 rc94_B3).Nonempty := by
-- proof
  apply StatMech.Walls.rc94_A3_B3_disjOcc_nonempty

/--
[rc94_nonmono_witness_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_nonmono_witness_fin3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG rc94_A3 rc94_B3).card ≤ (rc80_reflInterG rc94_A3 rc94_B3).card := by
-- proof
  apply StatMech.Walls.rc94_nonmono_witness_fin3

/--
[rc94_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean)
-/
@[path]
private lemma rc94_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), (rc80_reflInterG A B).card = (rc80_reflInterG B A).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc94_InterCoverA A B → A ∩ B ⊆ rc80_reflInterG B A) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc94_InterCoverA A B → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc90_ComplClosed A → rc94_InterCoverA A B) ∧ (¬ rc80_IsUpper rc94_A3 ∧ ¬ rc80_IsLower rc94_A3 ∧ ¬ rc80_IsUpper rc94_B3 ∧ ¬ rc80_IsLower rc94_B3 ∧ rc94_A3.card = 3 ∧ rc94_B3.card = 5 ∧ (rc94_A3 ∩ rc94_B3).Nonempty ∧ rc94_InterCoverA rc94_A3 rc94_B3 ∧ ¬ rc93_InterCover rc94_A3 rc94_B3 ∧ ¬ (rc94_A3 ∩ rc94_B3 ⊆ rc80_reflInterG rc94_A3 rc94_B3) ∧ ¬ rc90_ReflCover rc94_A3 rc94_B3 ∧ (rc80_disjOccG rc94_A3 rc94_B3).Nonempty ∧ (rc80_disjOccG rc94_A3 rc94_B3).card ≤ (rc80_reflInterG rc94_A3 rc94_B3).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc94_status


-- created on 2026-10-23
