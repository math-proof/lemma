import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
open Finset StatMech StatMech.Walls


/--
[rc38_doubleCompress_boxDoubled_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_doubleCompress_boxDoubled_card_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (doubleCompress i (boxDoubled 𝒜 ℬ)).card = (boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc38_doubleCompress_boxDoubled_card i 𝒜 ℬ

/--
[rc38_reflInter_le_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_reflInter_le_boxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (rc10_reflInter 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc38_reflInter_le_boxDoubled 𝒜 ℬ

/--
[rc38_boxDoubled_card_eq_dpairsCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_boxDoubled_card_eq_dpairsCount_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc38_boxDoubled_card_eq_dpairsCount 𝒜 ℬ

/--
[rc38_boxDoubled_singletonEmpty_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_boxDoubled_singletonEmpty_fin1_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (boxDoubled ({∅} : Finset (Finset (Fin 1))) ({∅})).card = 1 := by
-- proof
  apply StatMech.Walls.rc38_boxDoubled_singletonEmpty_fin1

/--
[rc38_reflInter_singletonEmpty_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_reflInter_singletonEmpty_fin1_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc10_reflInter ({∅} : Finset (Finset (Fin 1))) ({∅})).card = 0 := by
-- proof
  apply StatMech.Walls.rc38_reflInter_singletonEmpty_fin1

/--
[rc38_boxDoubled_le_reflInter_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_boxDoubled_le_reflInter_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (∀ (𝒜 ℬ : Finset (Finset (Fin 1))), (boxDoubled 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card) := by
-- proof
  apply StatMech.Walls.rc38_boxDoubled_le_reflInter_false

/--
[rc38_boxDoubled_le_reflInter_false_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_boxDoubled_le_reflInter_false_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), (boxDoubled 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card) := by
-- proof
  apply StatMech.Walls.rc38_boxDoubled_le_reflInter_false_fin3

/--
[rc38_insert_inr_dbl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_insert_inr_dbl_eq
  [Fintype α]
  [DecidableEq α]
  {S T : Finset α}
  {i : α} :
-- imply
  insert (Sum.inr i) (dbl S T) = dbl S (insert i T) := by
-- proof
  apply StatMech.Walls.rc38_insert_inr_dbl S T i

/--
[rc38_boxDoubled_isDownAtLeft_cex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_boxDoubled_isDownAtLeft_cex_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  IsDownAtLeft (0 : Fin 1) (boxDoubled ({∅}) ({∅, {0}})) := by
-- proof
  apply StatMech.Walls.rc38_boxDoubled_isDownAtLeft_cex

/--
[rc38_boxDoubled_isUpAtRight_cex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_boxDoubled_isUpAtRight_cex_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  IsUpAtRight (0 : Fin 1) (boxDoubled ({∅}) ({∅, {0}} : Finset (Finset (Fin 1)))) := by
-- proof
  apply StatMech.Walls.rc38_boxDoubled_isUpAtRight_cex

/--
[rc38_boxDoubled_doubleCompress_fixed_cex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_boxDoubled_doubleCompress_fixed_cex_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  doubleCompress (0 : Fin 1) (boxDoubled ({∅}) ({∅, {0}})) = boxDoubled ({∅}) ({∅, {0}}) := by
-- proof
  apply StatMech.Walls.rc38_boxDoubled_doubleCompress_fixed_cex

/--
[rc38_dblEmpty_mem_boxDoubled_cex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_dblEmpty_mem_boxDoubled_cex_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  dbl (∅ : Finset (Fin 1)) ∅ ∈ boxDoubled ({∅}) ({∅, {0}}) := by
-- proof
  apply StatMech.Walls.rc38_dblEmpty_mem_boxDoubled_cex

/--
[rc38_dblEmpty_notMem_complBoxDoubled_cex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_dblEmpty_notMem_complBoxDoubled_cex_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  dbl (∅ : Finset (Fin 1)) ∅ ∉ rc37_complBoxDoubled ({∅}) ({∅, {0}}) := by
-- proof
  apply StatMech.Walls.rc38_dblEmpty_notMem_complBoxDoubled_cex

/--
[rc38_fixed_boxDoubled_not_cubefilling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_fixed_boxDoubled_not_cubefilling_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ (𝒜 ℬ : Finset (Finset (Fin 1))) (i : Fin 1) (U : Finset (Fin 1 ⊕ Fin 1)), doubleCompress i (boxDoubled 𝒜 ℬ) = boxDoubled 𝒜 ℬ ∧ U ∈ boxDoubled 𝒜 ℬ ∧ U ∉ rc37_complBoxDoubled 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc38_fixed_boxDoubled_not_cubefilling

/--
[rc38_reimer_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_reimer_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc38_reimer_of_hallDoubled h

/--
[rc38_famCylBoxResidue_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_famCylBoxResidue_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc38_famCylBoxResidue_of_hallDoubled h

/--
[rc38_reimer_butterfly_deadend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc38butterflymono.lean)
-/
@[path]
private lemma rc38_reimer_butterfly_deadend_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (i : Fin 1) (𝒜 ℬ : Finset (Finset (Fin 1))), (doubleCompress i (boxDoubled 𝒜 ℬ)).card = (boxDoubled 𝒜 ℬ).card) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), (rc10_reflInter 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card) ∧ (¬ (∀ (𝒜 ℬ : Finset (Finset (Fin 1))), (boxDoubled 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card)) ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 1))) (i : Fin 1) (U : Finset (Fin 1 ⊕ Fin 1)), doubleCompress i (boxDoubled 𝒜 ℬ) = boxDoubled 𝒜 ℬ ∧ U ∈ boxDoubled 𝒜 ℬ ∧ U ∉ rc37_complBoxDoubled 𝒜 ℬ) ∧ (rc37_HallDoubled → rc18_CylBoxReflInter) ∧ (rc37_HallDoubled → rc20_FamCylBoxResidue) := by
-- proof
  apply StatMech.Walls.rc38_reimer_butterfly_deadend


-- created on 2026-10-23
