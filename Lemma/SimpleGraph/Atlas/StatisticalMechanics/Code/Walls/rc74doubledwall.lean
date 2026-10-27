import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
open Finset StatMech StatMech.Walls


/--
[rc74_reflInter_le_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_reflInter_le_boxDoubled_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (rc10_reflInter 𝒜 ℬ).card ≤ (StatMech.boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc74_reflInter_le_boxDoubled 𝒜 ℬ

/--
[rc74_boxDoubled_doubleCompress_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_boxDoubled_doubleCompress_invariant_eq
  {n : ℕ}
  {i : Fin n}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card = (StatMech.boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc74_boxDoubled_doubleCompress_invariant i 𝒜 ℬ

/--
[rc74_boxDoubled_gt_reflInter_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_boxDoubled_gt_reflInter_fin2_eq
  {n : ℕ} :
-- imply
  (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}).card = 1 ∧ (rc10_reflInter ({∅} : Finset (Finset (Fin 2))) {∅}).card = 0 ∧ (rc20_famCylBoxComp 2 ({∅} : Finset (Finset (Fin 2))) {∅}).card = 0 := by
-- proof
  apply StatMech.Walls.rc74_boxDoubled_gt_reflInter_fin2

/--
[rc74_boxDoubled_gt_famCylBox_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_boxDoubled_gt_famCylBox_fin2_eq
  {n : ℕ} :
-- imply
  (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 3 ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0 ∧ (rc10_reflInter ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0 := by
-- proof
  apply StatMech.Walls.rc74_boxDoubled_gt_famCylBox_fin2

/--
[rc74_boxDoubled_mem_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_boxDoubled_mem_disjoint_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {U : Finset (Fin n ⊕ Fin n)}
-- given
  (hU : U ∈ StatMech.boxDoubled 𝒜 ℬ) :
-- imply
  ∃ S T : Finset (Fin n), Disjoint S T ∧ StatMech.dbl S T = U := by
-- proof
  apply StatMech.Walls.rc74_boxDoubled_mem_disjoint 𝒜 ℬ hU

/--
[rc74_doubleCompress_breaks_encoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_doubleCompress_breaks_encoding_eq
  {n : ℕ} :
-- imply
  StatMech.dbl ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2)) ∈ StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}) ∧ ¬ Disjoint ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2)) := by
-- proof
  apply StatMech.Walls.rc74_doubleCompress_breaks_encoding

/--
[rc74_no_boxDoubled_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_no_boxDoubled_sandwich_eq
  {n : ℕ}
  {Φbox reflC boxdblC : ℕ}
-- given
  (hsand : Φbox ≤ reflC)
  (heq : Φbox = boxdblC)
  (hover : reflC < boxdblC) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.rc74_no_boxDoubled_sandwich Φbox reflC boxdblC hsand heq hover

/--
[rc74_boxDoubled_not_sandwich_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_boxDoubled_not_sandwich_fin2_eq
  {n : ℕ}
  {Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ}
-- given
  (hhi : ∀ p, Φ p ≤ (rc10_reflInter p.1 p.2).card)
  (heq : Φ (({∅} : Finset (Finset (Fin 2))), {∅}) = (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}).card) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.rc74_boxDoubled_not_sandwich_fin2 Φ hhi heq

/--
[rc74_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc74_reimerWprobCore_of_boxUnionBound h

/--
[rc74_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc74doubledwall.lean)
-/
@[path]
private lemma rc74_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), (rc10_reflInter 𝒜 ℬ).card ≤ (StatMech.boxDoubled 𝒜 ℬ).card) ∧ ((StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}).card = 1 ∧ (rc10_reflInter ({∅} : Finset (Finset (Fin 2))) {∅}).card = 0) ∧ ((StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 3 ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0) ∧ (∀ (m : ℕ) (i : Fin m) (𝒜 ℬ : Finset (Finset (Fin m))), (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card = (StatMech.boxDoubled 𝒜 ℬ).card) ∧ (StatMech.dbl ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2)) ∈ StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}) ∧ ¬ Disjoint ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2))) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc74_status


-- created on 2026-10-23
