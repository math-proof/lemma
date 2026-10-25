import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc90self.Part4
open Finset StatMech StatMech.Walls


/--
[rc90_reflInterG_eq_left_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_reflInterG_eq_left_of_cover_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc90_ReflCover A B) :
-- imply
  rc80_reflInterG A B = A := by
-- proof
  apply StatMech.Walls.rc90_reflInterG_eq_left_of_cover A B h

/--
[rc90_wall_reflCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_wall_reflCover_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : rc90_ReflCover A B) :
-- imply
  (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
-- proof
  apply StatMech.Walls.rc90_wall_reflCover A B h

/--
[rc90_reflCover_self_of_complClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_reflCover_self_of_complClosed_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
-- given
  (h : rc90_ComplClosed A) :
-- imply
  rc90_ReflCover A A := by
-- proof
  apply StatMech.Walls.rc90_reflCover_self_of_complClosed A h

/--
[rc90_wall_self_complClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_wall_self_complClosed_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
-- given
  (h : rc90_ComplClosed A) :
-- imply
  (rc80_disjOccG A A).card ≤ (rc80_reflInterG A A).card := by
-- proof
  apply StatMech.Walls.rc90_wall_self_complClosed A h

/--
[rc90_reflInterG_self_eq_of_complClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_reflInterG_self_eq_of_complClosed_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
-- given
  (h : rc90_ComplClosed A) :
-- imply
  rc80_reflInterG A A = A := by
-- proof
  apply StatMech.Walls.rc90_reflInterG_self_eq_of_complClosed A h

/--
[rc90_Aself_not_complClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_Aself_not_complClosed_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc90_ComplClosed rc90_Aself := by
-- proof
  apply StatMech.Walls.rc90_Aself_not_complClosed

/--
[rc90_self_diagonal_true_but_needs_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_self_diagonal_true_but_needs_injection_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ (rc80_disjOccG rc90_Aself rc90_Aself ⊆ rc80_reflInterG rc90_Aself rc90_Aself) := by
-- proof
  apply StatMech.Walls.rc90_self_diagonal_true_but_needs_injection

/--
[rc90_A3_B3_reflCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_A3_B3_reflCover_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc90_ReflCover rc90_A3 rc90_B3 := by
-- proof
  apply StatMech.Walls.rc90_A3_B3_reflCover

/--
[rc90_A3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_A3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc90_A3 := by
-- proof
  apply StatMech.Walls.rc90_A3_not_upper

/--
[rc90_A3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_A3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc90_A3 := by
-- proof
  apply StatMech.Walls.rc90_A3_not_lower

/--
[rc90_B3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_B3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc90_B3 := by
-- proof
  apply StatMech.Walls.rc90_B3_not_upper

/--
[rc90_B3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_B3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc90_B3 := by
-- proof
  apply StatMech.Walls.rc90_B3_not_lower

/--
[rc90_A3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_A3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc90_A3.card = 3 := by
-- proof
  apply StatMech.Walls.rc90_A3_card

/--
[rc90_B3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_B3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc90_B3.card = 5 := by
-- proof
  apply StatMech.Walls.rc90_B3_card

/--
[rc90_A3_B3_disjOcc_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_A3_B3_disjOcc_nonempty_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG rc90_A3 rc90_B3).Nonempty := by
-- proof
  apply StatMech.Walls.rc90_A3_B3_disjOcc_nonempty

/--
[rc90_nonmono_witness_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_nonmono_witness_fin3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG rc90_A3 rc90_B3).card ≤ (rc80_reflInterG rc90_A3 rc90_B3).card := by
-- proof
  apply StatMech.Walls.rc90_nonmono_witness_fin3

/--
[rc90_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean)
-/
@[path]
private lemma rc90_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc90_ReflCover A B → rc80_reflInterG A B = A) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc90_ReflCover A B → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), rc90_ComplClosed A → (rc80_disjOccG A A).card ≤ (rc80_reflInterG A A).card) ∧ (¬ (rc80_disjOccG rc90_Aself rc90_Aself ⊆ rc80_reflInterG rc90_Aself rc90_Aself)) ∧ (¬ rc80_IsUpper rc90_A3 ∧ ¬ rc80_IsLower rc90_A3 ∧ ¬ rc80_IsUpper rc90_B3 ∧ ¬ rc80_IsLower rc90_B3 ∧ rc90_A3.card = 3 ∧ rc90_B3.card = 5 ∧ rc90_ReflCover rc90_A3 rc90_B3 ∧ (rc80_disjOccG rc90_A3 rc90_B3).Nonempty ∧ (rc80_disjOccG rc90_A3 rc90_B3).card ≤ (rc80_reflInterG rc90_A3 rc90_B3).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc90_status


-- created on 2026-10-23
