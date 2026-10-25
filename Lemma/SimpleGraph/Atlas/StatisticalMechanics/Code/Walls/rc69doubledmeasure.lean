import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc69doubledmeasure.Part2
open Finset StatMech StatMech.Walls


/--
[rc69_boxDoubled_card_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_boxDoubled_card_le_mul_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (StatMech.boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card ∧ (StatMech.boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card := by
-- proof
  apply StatMech.Walls.rc69_boxDoubled_card_le_mul 𝒜 ℬ

/--
[rc69_boxDoubled_unrelated_to_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_boxDoubled_unrelated_to_wall_eq
  {n : ℕ} :
-- imply
  (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 3 ∧ ({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card = 4 ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0 ∧ (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0 := by
-- proof
  apply StatMech.Walls.rc69_boxDoubled_unrelated_to_wall

/--
[rc69_fixpoint_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_fixpoint_wall_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))}
-- given
  (hd : rc62_isDown 2 𝒜 = true)
  (hu : rc62_isUp 2 ℬ = true) :
-- imply
  (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc69_fixpoint_wall 𝒜 ℬ hd hu

/--
[rc69_reflInter_grows_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_reflInter_grows_witness_eq
  {n : ℕ} :
-- imply
  (rc20_reflInterComp 2 (rc61_dnA 0 ({∅} : Finset (Finset (Fin 2)))) (rc61_upB 0 ({{1}} : Finset (Finset (Fin 2))))).card = 1 ∧ (rc20_reflInterComp 2 ({∅} : Finset (Finset (Fin 2))) ({{1}})).card = 0 := by
-- proof
  apply StatMech.Walls.rc69_reflInter_grows_witness

/--
[rc69_downCompression_not_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_downCompression_not_injective_eq
  {n : ℕ} :
-- imply
  Down.compression 0 ({∅} : Finset (Finset (Fin 2))) = Down.compression 0 ({{0}} : Finset (Finset (Fin 2))) ∧ ({∅} : Finset (Finset (Fin 2))) ≠ ({{0}} : Finset (Finset (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc69_downCompression_not_injective

/--
[rc69_transportBack_forces_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_transportBack_forces_card_le_eq
  {n : ℕ}
  {X Y : Finset α}
  {g : α → α}
-- given
  (hginj : Set.InjOn g X)
  (hgmem : ∀ a ∈ X, g a ∈ Y) :
-- imply
  X.card ≤ Y.card := by
-- proof
  apply StatMech.Walls.rc69_transportBack_forces_card_le X Y g hginj hgmem

/--
[rc69_transportBack_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_transportBack_refuted_eq
  {n : ℕ} :
-- imply
  ¬ ∃ g : Finset (Fin 2) → Finset (Fin 2), Set.InjOn g (rc20_reflInterComp 2 (rc61_dnA 0 ({∅} : Finset (Finset (Fin 2)))) (rc61_upB 0 ({{1}}))) ∧ (∀ R ∈ rc20_reflInterComp 2 (rc61_dnA 0 ({∅} : Finset (Finset (Fin 2)))) (rc61_upB 0 ({{1}})), g R ∈ rc20_reflInterComp 2 ({∅} : Finset (Finset (Fin 2))) ({{1}})) := by
-- proof
  apply StatMech.Walls.rc69_transportBack_refuted

/--
[rc69_residue_eq_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_residue_eq_boxUnionBound_eq
  {n : ℕ} :
-- imply
  rc69_DoubledMeasureResidue = rc60_BoxUnionBound := by
-- proof
  apply StatMech.Walls.rc69_residue_eq_boxUnionBound

/--
[rc69_reimerWprobCore_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_reimerWprobCore_of_residue_eq
  {n : ℕ}
-- given
  (h : rc69_DoubledMeasureResidue) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc69_reimerWprobCore_of_residue h

/--
[rc69_residue_of_indepHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_residue_of_indepHall_eq
  {n : ℕ}
-- given
  (h : rc59_IndepHall) :
-- imply
  rc69_DoubledMeasureResidue := by
-- proof
  apply StatMech.Walls.rc69_residue_of_indepHall h

/--
[rc69_residue_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_residue_fin2_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc69_residue_fin2 𝒜 ℬ

/--
[rc69_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean)
-/
@[path]
private lemma rc69_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), (StatMech.boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card) ∧ ((StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 3 ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0 ∧ (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0) ∧ ((rc20_reflInterComp 2 (rc61_dnA 0 ({∅} : Finset (Finset (Fin 2)))) (rc61_upB 0 ({{1}}))).card = 1 ∧ (rc20_reflInterComp 2 ({∅} : Finset (Finset (Fin 2))) ({{1}})).card = 0) ∧ (Down.compression 0 ({∅} : Finset (Finset (Fin 2))) = Down.compression 0 ({{0}} : Finset (Finset (Fin 2))) ∧ ({∅} : Finset (Finset (Fin 2))) ≠ ({{0}} : Finset (Finset (Fin 2)))) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true → (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧ (rc69_DoubledMeasureResidue → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc69_status


-- created on 2026-10-23
