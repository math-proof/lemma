import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc87extra.Part2
open Finset StatMech StatMech.Walls


/--
[rc87_occ_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_occ_univ_eq
  [Fintype ι]
  [DecidableEq ι]
  {K : Finset ι}
  {w : ConfigSpace ι} :
-- imply
  rc80_occ (Finset.univ : Finset (ConfigSpace ι)) K w = true := by
-- proof
  apply StatMech.Walls.rc87_occ_univ K w

/--
[rc87_occ_self_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_occ_self_mem_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)}
  {L : Finset ι}
  {w : ConfigSpace ι}
-- given
  (h : rc80_occ B L w = true) :
-- imply
  w ∈ B := by
-- proof
  apply StatMech.Walls.rc87_occ_self_mem B L w h

/--
[rc87_disjOccG_univ_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_disjOccG_univ_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B = B := by
-- proof
  apply StatMech.Walls.rc87_disjOccG_univ_left B

/--
[rc87_disjOccG_univ_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_disjOccG_univ_right_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι)) = A := by
-- proof
  apply StatMech.Walls.rc87_disjOccG_univ_right A

/--
[rc87_compl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_compl_injective_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  Function.Injective (rc80_compl : ConfigSpace ι → ConfigSpace ι) := by
-- proof
  apply StatMech.Walls.rc87_compl_injective

/--
[rc87_reflInterG_univ_left_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_reflInterG_univ_left_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B = B.image rc80_compl := by
-- proof
  apply StatMech.Walls.rc87_reflInterG_univ_left_eq B

/--
[rc87_reflInterG_univ_left_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_reflInterG_univ_left_card_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card = B.card := by
-- proof
  apply StatMech.Walls.rc87_reflInterG_univ_left_card B

/--
[rc87_reflInterG_univ_right_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_reflInterG_univ_right_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι)) = A := by
-- proof
  apply StatMech.Walls.rc87_reflInterG_univ_right_eq A

/--
[rc87_reflInterG_univ_right_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_reflInterG_univ_right_card_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card = A.card := by
-- proof
  apply StatMech.Walls.rc87_reflInterG_univ_right_card A

/--
[rc87_wall_univ_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_wall_univ_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card := by
-- proof
  apply StatMech.Walls.rc87_wall_univ_left B

/--
[rc87_wall_univ_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_wall_univ_right_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card := by
-- proof
  apply StatMech.Walls.rc87_wall_univ_right A

/--
[rc87_wall_univ_left_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_wall_univ_left_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card = (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card := by
-- proof
  apply StatMech.Walls.rc87_wall_univ_left_eq B

/--
[rc87_B3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_B3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc87_B3 := by
-- proof
  apply StatMech.Walls.rc87_B3_not_upper

/--
[rc87_B3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_B3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc87_B3 := by
-- proof
  apply StatMech.Walls.rc87_B3_not_lower

/--
[rc87_nonmono_witness_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_nonmono_witness_fin3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card = (rc80_reflInterG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card := by
-- proof
  apply StatMech.Walls.rc87_nonmono_witness_fin3

/--
[rc87_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean)
-/
@[path]
private lemma rc87_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B = B) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι)) = A) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card = B.card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι)) = A) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card) ∧ (¬ rc80_IsUpper rc87_B3 ∧ ¬ rc80_IsLower rc87_B3 ∧ (rc80_disjOccG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card = (rc80_reflInterG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc87_status


-- created on 2026-10-23
