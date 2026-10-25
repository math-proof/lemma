import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc93extra.Part2
open Finset StatMech StatMech.Walls


/--
[rc93_inter_subset_reflInterG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_inter_subset_reflInterG_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc93_InterCover A B) :
-- imply
  A ∩ B ⊆ rc80_reflInterG A B := by
-- proof
  apply StatMech.Walls.rc93_inter_subset_reflInterG A B h

/--
[rc93_disjOccG_subset_reflInterG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_disjOccG_subset_reflInterG_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc93_InterCover A B) :
-- imply
  rc80_disjOccG A B ⊆ rc80_reflInterG A B := by
-- proof
  apply StatMech.Walls.rc93_disjOccG_subset_reflInterG A B h

/--
[rc93_wall_interCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_wall_interCover_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc93_InterCover A B) :
-- imply
  (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
-- proof
  apply StatMech.Walls.rc93_wall_interCover A B h

/--
[rc93_interCover_of_reflCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_interCover_of_reflCover_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc90_ReflCover A B) :
-- imply
  rc93_InterCover A B := by
-- proof
  apply StatMech.Walls.rc93_interCover_of_reflCover A B h

/--
[rc93_A3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_A3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc93_A3 := by
-- proof
  apply StatMech.Walls.rc93_A3_not_upper

/--
[rc93_A3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_A3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc93_A3 := by
-- proof
  apply StatMech.Walls.rc93_A3_not_lower

/--
[rc93_B3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_B3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc93_B3 := by
-- proof
  apply StatMech.Walls.rc93_B3_not_upper

/--
[rc93_B3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_B3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc93_B3 := by
-- proof
  apply StatMech.Walls.rc93_B3_not_lower

/--
[rc93_A3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_A3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc93_A3.card = 5 := by
-- proof
  apply StatMech.Walls.rc93_A3_card

/--
[rc93_B3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_B3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc93_B3.card = 3 := by
-- proof
  apply StatMech.Walls.rc93_B3_card

/--
[rc93_A3_B3_inter_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_A3_B3_inter_nonempty_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc93_A3 ∩ rc93_B3).Nonempty := by
-- proof
  apply StatMech.Walls.rc93_A3_B3_inter_nonempty

/--
[rc93_A3_B3_interCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_A3_B3_interCover_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc93_InterCover rc93_A3 rc93_B3 := by
-- proof
  apply StatMech.Walls.rc93_A3_B3_interCover

/--
[rc93_A3_B3_not_reflCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_A3_B3_not_reflCover_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc90_ReflCover rc93_A3 rc93_B3 := by
-- proof
  apply StatMech.Walls.rc93_A3_B3_not_reflCover

/--
[rc93_A3_B3_reflInterG_ne_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_A3_B3_reflInterG_ne_A_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc80_reflInterG rc93_A3 rc93_B3 ≠ rc93_A3 := by
-- proof
  apply StatMech.Walls.rc93_A3_B3_reflInterG_ne_A

/--
[rc93_A3_B3_disjOcc_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_A3_B3_disjOcc_nonempty_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG rc93_A3 rc93_B3).Nonempty := by
-- proof
  apply StatMech.Walls.rc93_A3_B3_disjOcc_nonempty

/--
[rc93_nonmono_witness_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_nonmono_witness_fin3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG rc93_A3 rc93_B3).card ≤ (rc80_reflInterG rc93_A3 rc93_B3).card := by
-- proof
  apply StatMech.Walls.rc93_nonmono_witness_fin3

/--
[rc93_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean)
-/
@[path]
private lemma rc93_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc93_InterCover A B → A ∩ B ⊆ rc80_reflInterG A B) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc93_InterCover A B → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc90_ReflCover A B → rc93_InterCover A B) ∧ (¬ rc80_IsUpper rc93_A3 ∧ ¬ rc80_IsLower rc93_A3 ∧ ¬ rc80_IsUpper rc93_B3 ∧ ¬ rc80_IsLower rc93_B3 ∧ rc93_A3.card = 5 ∧ rc93_B3.card = 3 ∧ (rc93_A3 ∩ rc93_B3).Nonempty ∧ rc93_InterCover rc93_A3 rc93_B3 ∧ ¬ rc90_ReflCover rc93_A3 rc93_B3 ∧ rc80_reflInterG rc93_A3 rc93_B3 ≠ rc93_A3 ∧ (rc80_disjOccG rc93_A3 rc93_B3).Nonempty ∧ (rc80_disjOccG rc93_A3 rc93_B3).card ≤ (rc80_reflInterG rc93_A3 rc93_B3).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc93_status


-- created on 2026-10-23
