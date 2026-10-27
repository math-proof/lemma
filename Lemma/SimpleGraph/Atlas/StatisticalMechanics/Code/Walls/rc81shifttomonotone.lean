import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc81shifttomonotone.Part3
open Finset StatMech StatMech.Walls


/--
[rc81_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_le_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {w v : ConfigSpace ι} :
-- imply
  rc81_le w v = true ↔ ∀ i, w i = true → v i = true := by
-- proof
  apply StatMech.Walls.rc81_le_iff w v

/--
[rc81_mem_upClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_mem_upClosure_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
  {w : ConfigSpace ι} :
-- imply
  w ∈ rc81_upClosure A ↔ ∃ a ∈ A, rc81_le a w = true := by
-- proof
  apply StatMech.Walls.rc81_mem_upClosure w

/--
[rc81_mem_downClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_mem_downClosure_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)}
  {w : ConfigSpace ι} :
-- imply
  w ∈ rc81_downClosure B ↔ ∃ b ∈ B, rc81_le w b = true := by
-- proof
  apply StatMech.Walls.rc81_mem_downClosure w

/--
[rc81_subset_upClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_subset_upClosure_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  A ⊆ rc81_upClosure A := by
-- proof
  apply StatMech.Walls.rc81_subset_upClosure A

/--
[rc81_subset_downClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_subset_downClosure_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  B ⊆ rc81_downClosure B := by
-- proof
  apply StatMech.Walls.rc81_subset_downClosure B

/--
[rc81_upClosure_isUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_upClosure_isUpper_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  rc80_IsUpper (rc81_upClosure A) := by
-- proof
  apply StatMech.Walls.rc81_upClosure_isUpper A

/--
[rc81_downClosure_isLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_downClosure_isLower_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  rc80_IsLower (rc81_downClosure B) := by
-- proof
  apply StatMech.Walls.rc81_downClosure_isLower B

/--
[rc81_reflInter_mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_reflInter_mono_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {A A' B : Finset (ConfigSpace ι)}
-- given
  (h : A ⊆ A') :
-- imply
  rc80_reflInterG A B ⊆ rc80_reflInterG A' B := by
-- proof
  apply StatMech.Walls.rc81_reflInter_mono_left h

/--
[rc81_upClosure_reflInter_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_upClosure_reflInter_ge_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_reflInterG A B).card ≤ (rc80_reflInterG (rc81_upClosure A) B).card := by
-- proof
  apply StatMech.Walls.rc81_upClosure_reflInter_ge A B

/--
[rc81_reflInter_orig_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_reflInter_orig_zero_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_reflInterG rc81_wA rc81_wA).card = 0 := by
-- proof
  apply StatMech.Walls.rc81_reflInter_orig_zero

/--
[rc81_wA_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_wA_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc81_wA := by
-- proof
  apply StatMech.Walls.rc81_wA_not_upper

/--
[rc81_upClosure_wA_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_upClosure_wA_univ_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc81_upClosure rc81_wA = (Finset.univ : Finset (ConfigSpace (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc81_upClosure_wA_univ

/--
[rc81_reflInter_shifted_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_reflInter_shifted_one_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_reflInterG (rc81_upClosure rc81_wA) rc81_wA).card = 1 := by
-- proof
  apply StatMech.Walls.rc81_reflInter_shifted_one

/--
[rc81_shift_refutes_wall_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_shift_refutes_wall_witness_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_reflInterG rc81_wA rc81_wA).card < (rc80_reflInterG (rc81_upClosure rc81_wA) rc81_wA).card := by
-- proof
  apply StatMech.Walls.rc81_shift_refutes_wall_witness

/--
[rc81_occ_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_occ_mono_eq
  [Fintype ι]
  [DecidableEq ι]
  {A A' : Finset (ConfigSpace ι)}
  {K : Finset ι}
  {w : ConfigSpace ι}
-- given
  (h : A ⊆ A')
  (hocc : rc80_occ A K w = true) :
-- imply
  rc80_occ A' K w = true := by
-- proof
  apply StatMech.Walls.rc81_occ_mono h K w hocc

/--
[rc81_disjOcc_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_disjOcc_mono_eq
  [Fintype ι]
  [DecidableEq ι]
  {A A' B B' : Finset (ConfigSpace ι)}
-- given
  (hA : A ⊆ A')
  (hB : B ⊆ B') :
-- imply
  rc80_disjOccG A B ⊆ rc80_disjOccG A' B' := by
-- proof
  apply StatMech.Walls.rc81_disjOcc_mono hA hB

/--
[rc81_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_reimerWprobCore_of_boxUnionBound_eq
  [Fintype ι]
  [DecidableEq ι]
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc81_reimerWprobCore_of_boxUnionBound h

/--
[rc81_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean)
-/
@[path]
private lemma rc81_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), rc80_IsUpper (rc81_upClosure A)) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), rc80_IsLower (rc81_downClosure B)) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), (rc80_reflInterG A B).card ≤ (rc80_reflInterG (rc81_upClosure A) B).card) ∧ ((rc80_reflInterG rc81_wA rc81_wA).card < (rc80_reflInterG (rc81_upClosure rc81_wA) rc81_wA).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A A' B B' : Finset (ConfigSpace ι)}, A ⊆ A' → B ⊆ B' → rc80_disjOccG A B ⊆ rc80_disjOccG A' B') ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc81_status


-- created on 2026-10-23
