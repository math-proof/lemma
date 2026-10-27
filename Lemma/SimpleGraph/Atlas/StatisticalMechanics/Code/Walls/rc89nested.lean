import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc89nested.Part3
open Finset StatMech StatMech.Walls


/--
[rc89_occ_self_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_occ_self_mem_eq
  [Fintype ι]
  [DecidableEq ι]
  {X : Finset (ConfigSpace ι)}
  {S : Finset ι}
  {w : ConfigSpace ι}
-- given
  (h : rc80_occ X S w = true) :
-- imply
  w ∈ X := by
-- proof
  apply StatMech.Walls.rc89_occ_self_mem X S w h

/--
[rc89_disjOccG_subset_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_disjOccG_subset_inter_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG A B ⊆ A ∩ B := by
-- proof
  apply StatMech.Walls.rc89_disjOccG_subset_inter A B

/--
[rc89_disjOccG_eq_empty_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_disjOccG_eq_empty_of_disjoint_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : A ∩ B = ∅) :
-- imply
  rc80_disjOccG A B = ∅ := by
-- proof
  apply StatMech.Walls.rc89_disjOccG_eq_empty_of_disjoint A B h

/--
[rc89_wall_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_wall_disjoint_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)}
-- given
  (h : A ∩ B = ∅) :
-- imply
  (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
-- proof
  apply StatMech.Walls.rc89_wall_disjoint A B h

/--
[rc89_inter_setCompl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_inter_setCompl_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  A ∩ rc89_setCompl A = ∅ := by
-- proof
  apply StatMech.Walls.rc89_inter_setCompl A

/--
[rc89_wall_setcompl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_wall_setcompl_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card := by
-- proof
  apply StatMech.Walls.rc89_wall_setcompl A

/--
[rc89_A3_inter_B3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_A3_inter_B3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc89_A3 ∩ rc89_B3 = ∅ := by
-- proof
  apply StatMech.Walls.rc89_A3_inter_B3

/--
[rc89_A3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_A3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc89_A3 := by
-- proof
  apply StatMech.Walls.rc89_A3_not_upper

/--
[rc89_A3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_A3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc89_A3 := by
-- proof
  apply StatMech.Walls.rc89_A3_not_lower

/--
[rc89_B3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_B3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc89_B3 := by
-- proof
  apply StatMech.Walls.rc89_B3_not_upper

/--
[rc89_B3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_B3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc89_B3 := by
-- proof
  apply StatMech.Walls.rc89_B3_not_lower

/--
[rc89_A3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_A3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc89_A3.card = 3 := by
-- proof
  apply StatMech.Walls.rc89_A3_card

/--
[rc89_B3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_B3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc89_B3.card = 3 := by
-- proof
  apply StatMech.Walls.rc89_B3_card

/--
[rc89_nonmono_witness_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_nonmono_witness_fin3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG rc89_A3 rc89_B3).card ≤ (rc80_reflInterG rc89_A3 rc89_B3).card := by
-- proof
  apply StatMech.Walls.rc89_nonmono_witness_fin3

/--
[rc89_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc89nested.lean)
-/
@[path]
private lemma rc89_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_disjOccG A B ⊆ A ∩ B) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), A ∩ B = ∅ → rc80_disjOccG A B = ∅) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), A ∩ B = ∅ → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card) ∧ (¬ rc80_IsUpper rc89_A3 ∧ ¬ rc80_IsLower rc89_A3 ∧ ¬ rc80_IsUpper rc89_B3 ∧ ¬ rc80_IsLower rc89_B3 ∧ rc89_A3.card = 3 ∧ rc89_B3.card = 3 ∧ rc89_A3 ∩ rc89_B3 = ∅ ∧ (rc80_disjOccG rc89_A3 rc89_B3).card ≤ (rc80_reflInterG rc89_A3 rc89_B3).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc89_status


-- created on 2026-10-23
