import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc92basecase.Part2
open Finset StatMech StatMech.Walls


/--
[rc92_wall_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_wall_fin2_eq :
-- imply
  ∀ A B : Finset (ConfigSpace (Fin 2)), (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
-- proof
  apply StatMech.Walls.rc92_wall_fin2

/--
[rc92_A0_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A0_card_eq :
-- imply
  rc92_A0.card = 3 := by
-- proof
  apply StatMech.Walls.rc92_A0_card

/--
[rc92_A1_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A1_card_eq :
-- imply
  rc92_A1.card = 3 := by
-- proof
  apply StatMech.Walls.rc92_A1_card

/--
[rc92_A2_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A2_card_eq :
-- imply
  rc92_A2.card = 3 := by
-- proof
  apply StatMech.Walls.rc92_A2_card

/--
[rc92_A0_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A0_not_upper_eq :
-- imply
  ¬ rc80_IsUpper rc92_A0 := by
-- proof
  apply StatMech.Walls.rc92_A0_not_upper

/--
[rc92_A0_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A0_not_lower_eq :
-- imply
  ¬ rc80_IsLower rc92_A0 := by
-- proof
  apply StatMech.Walls.rc92_A0_not_lower

/--
[rc92_A1_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A1_not_upper_eq :
-- imply
  ¬ rc80_IsUpper rc92_A1 := by
-- proof
  apply StatMech.Walls.rc92_A1_not_upper

/--
[rc92_A1_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A1_not_lower_eq :
-- imply
  ¬ rc80_IsLower rc92_A1 := by
-- proof
  apply StatMech.Walls.rc92_A1_not_lower

/--
[rc92_A2_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A2_not_upper_eq :
-- imply
  ¬ rc80_IsUpper rc92_A2 := by
-- proof
  apply StatMech.Walls.rc92_A2_not_upper

/--
[rc92_A2_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_A2_not_lower_eq :
-- imply
  ¬ rc80_IsLower rc92_A2 := by
-- proof
  apply StatMech.Walls.rc92_A2_not_lower

/--
[rc92_wall_fin3_A0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_wall_fin3_A0_eq :
-- imply
  ∀ B : Finset (ConfigSpace (Fin 3)), (rc80_disjOccG rc92_A0 B).card ≤ (rc80_reflInterG rc92_A0 B).card := by
-- proof
  apply StatMech.Walls.rc92_wall_fin3_A0

/--
[rc92_wall_fin3_A1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_wall_fin3_A1_eq :
-- imply
  ∀ B : Finset (ConfigSpace (Fin 3)), (rc80_disjOccG rc92_A1 B).card ≤ (rc80_reflInterG rc92_A1 B).card := by
-- proof
  apply StatMech.Walls.rc92_wall_fin3_A1

/--
[rc92_wall_fin3_A2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_wall_fin3_A2_eq :
-- imply
  ∀ B : Finset (ConfigSpace (Fin 3)), (rc80_disjOccG rc92_A2 B).card ≤ (rc80_reflInterG rc92_A2 B).card := by
-- proof
  apply StatMech.Walls.rc92_wall_fin3_A2

/--
[rc92_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean)
-/
@[path]
private lemma rc92_status_eq :
-- imply
  (∀ A B : Finset (ConfigSpace (Fin 2)), (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ B : Finset (ConfigSpace (Fin 3)), (rc80_disjOccG rc92_A0 B).card ≤ (rc80_reflInterG rc92_A0 B).card) ∧ (∀ B : Finset (ConfigSpace (Fin 3)), (rc80_disjOccG rc92_A1 B).card ≤ (rc80_reflInterG rc92_A1 B).card) ∧ (∀ B : Finset (ConfigSpace (Fin 3)), (rc80_disjOccG rc92_A2 B).card ≤ (rc80_reflInterG rc92_A2 B).card) ∧ (rc92_A0.card = 3 ∧ ¬ rc80_IsUpper rc92_A0 ∧ ¬ rc80_IsLower rc92_A0 ∧ rc92_A1.card = 3 ∧ ¬ rc80_IsUpper rc92_A1 ∧ ¬ rc80_IsLower rc92_A1 ∧ rc92_A2.card = 3 ∧ ¬ rc80_IsUpper rc92_A2 ∧ ¬ rc80_IsLower rc92_A2) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc92_status


-- created on 2026-10-23
