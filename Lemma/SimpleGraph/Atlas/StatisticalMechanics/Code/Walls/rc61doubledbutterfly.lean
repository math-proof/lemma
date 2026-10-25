import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc61doubledbutterfly.Part3
open Finset StatMech StatMech.Walls


/--
[rc61_boxDoubled_card_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_boxDoubled_card_invariant_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {i : Fin n} :
-- imply
  (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card = (StatMech.boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc61_boxDoubled_card_invariant 𝒜 ℬ i

/--
[rc61_boxDoubled_card_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_boxDoubled_card_le_mul_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (StatMech.boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card := by
-- proof
  apply StatMech.Walls.rc61_boxDoubled_card_le_mul 𝒜 ℬ

/--
[rc61_boxDoubled_card_eq_dpairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_boxDoubled_card_eq_dpairs_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (StatMech.boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card := by
-- proof
  apply StatMech.Walls.rc61_boxDoubled_card_eq_dpairs 𝒜 ℬ

/--
[rc61_reflInter_downUp_mono_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_reflInter_downUp_mono_fin2_eq
  {n : ℕ} :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), (rc20_reflInterComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc61_reflInter_downUp_mono_fin2

/--
[rc61_reflInter_downUp_mono_fin2_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_reflInter_downUp_mono_fin2_coord1_eq
  {n : ℕ} :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), (rc20_reflInterComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 (rc61_dnA 1 𝒜) (rc61_upB 1 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc61_reflInter_downUp_mono_fin2_coord1

/--
[rc61_famCylBox_downUp_mono_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_famCylBox_downUp_mono_fin2_eq
  {n : ℕ} :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_famCylBoxComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc61_famCylBox_downUp_mono_fin2

/--
[rc61_gap_not_downUp_mono_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_gap_not_downUp_mono_fin2_eq
  {n : ℕ} :
-- imply
  (rc20_reflInterComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card + (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card < (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card + (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card := by
-- proof
  apply StatMech.Walls.rc61_gap_not_downUp_mono_fin2

/--
[rc61_famCylBox_not_subset_reflInter_at_fixpoint_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_famCylBox_not_subset_reflInter_at_fixpoint_fin2_eq
  {n : ℕ} :
-- imply
  ¬ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} ⊆ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}}) := by
-- proof
  apply StatMech.Walls.rc61_famCylBox_not_subset_reflInter_at_fixpoint_fin2

/--
[rc61_fixpoint_witness_is_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_fixpoint_witness_is_fixed_eq
  {n : ℕ} :
-- imply
  Down.compression 0 ({∅, {0}} : Finset (Finset (Fin 2))) = {∅, {0}} ∧ Down.compression 1 ({∅, {0}} : Finset (Finset (Fin 2))) = {∅, {0}} ∧ UV.compression {0} ∅ ({{0}, {0, 1}} : Finset (Finset (Fin 2))) = {{0}, {0, 1}} ∧ UV.compression {1} ∅ ({{0}, {0, 1}} : Finset (Finset (Fin 2))) = {{0}, {0, 1}} := by
-- proof
  apply StatMech.Walls.rc61_fixpoint_witness_is_fixed

/--
[rc61_reimerWprobCore_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_reimerWprobCore_of_residue_eq
  {n : ℕ}
-- given
  (h : rc61_DoubledButterflyResidue) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc61_reimerWprobCore_of_residue h

/--
[rc61_residue_eq_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_residue_eq_boxUnionBound_eq
  {n : ℕ} :
-- imply
  rc61_DoubledButterflyResidue = rc60_BoxUnionBound := by
-- proof
  apply StatMech.Walls.rc61_residue_eq_boxUnionBound

/--
[rc61_wall_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_wall_of_residue_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc61_wall_of_residue 𝒜 ℬ h

/--
[rc61_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean)
-/
@[path]
private lemma rc61_status_eq
  {n : ℕ} :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2), (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card = (StatMech.boxDoubled 𝒜 ℬ).card) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), (rc20_reflInterComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card) ∧ ((rc20_reflInterComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card + (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card < (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card + (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card) ∧ (¬ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} ⊆ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}})) ∧ (rc61_DoubledButterflyResidue → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc61_status


-- created on 2026-10-23
