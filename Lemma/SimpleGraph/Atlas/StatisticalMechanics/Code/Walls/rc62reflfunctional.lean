import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc62reflfunctional.Part3
open Finset StatMech StatMech.Walls


/--
[rc62_reflInter_ge_box_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_reflInter_ge_box_fin2_eq
  {n : ℕ} :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc62_reflInter_ge_box_fin2

/--
[rc62_forward_chain_only_bounds_fixpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_forward_chain_only_bounds_fixpoint_eq
  {n : ℕ}
  {boxStart Φstart Φfix reflFix : ℕ}
-- given
  (ha : boxStart ≤ Φstart)
  (hc : Φstart ≤ Φfix)
  (hb : Φfix ≤ reflFix) :
-- imply
  boxStart ≤ reflFix := by
-- proof
  apply StatMech.Walls.rc62_forward_chain_only_bounds_fixpoint boxStart Φstart Φfix reflFix ha hc hb

/--
[rc62_forward_chain_strict_gap_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_forward_chain_strict_gap_fin2_eq
  {n : ℕ} :
-- imply
  (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card = 0 ∧ (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card = 1 ∧ (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card = 1 := by
-- proof
  apply StatMech.Walls.rc62_forward_chain_strict_gap_fin2

/--
[rc62_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_edge_eq
  {n : ℕ} :
-- imply
  rc62_step 0 rc62_node₁ = rc62_node₂ := by
-- proof
  apply StatMech.Walls.rc62_edge

/--
[rc62_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_edge_eq_2
  {n : ℕ} :
-- imply
  rc62_step 0 rc62_node₃ = rc62_node₂ := by
-- proof
  apply StatMech.Walls.rc62_edge

/--
[rc62_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_edge_eq_3
  {n : ℕ} :
-- imply
  rc62_step 1 rc62_node₃ = rc62_node₄ := by
-- proof
  apply StatMech.Walls.rc62_edge

/--
[rc62_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_edge_eq_4
  {n : ℕ} :
-- imply
  rc62_step 1 rc62_node₅ = rc62_node₄ := by
-- proof
  apply StatMech.Walls.rc62_edge

/--
[rc62_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_node_eq
  {n : ℕ} :
-- imply
  (rc20_famCylBoxComp 2 rc62_node₁.1 rc62_node₁.2).card = 1 := by
-- proof
  apply StatMech.Walls.rc62_node

/--
[rc62_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_node_eq_2
  {n : ℕ} :
-- imply
  (rc20_reflInterComp 2 rc62_node₅.1 rc62_node₅.2).card = 0 := by
-- proof
  apply StatMech.Walls.rc62_node

/--
[rc62_no_invariant_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_no_invariant_sandwich_eq
  {n : ℕ}
  {Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ}
-- given
  (hinv : ∀ (i : Fin 2) (p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2))), Φ (rc62_step i p) = Φ p)
  (hlo : ∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)), (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p)
  (hhi : ∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)), Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.rc62_no_invariant_sandwich Φ hinv hlo hhi

/--
[rc62_uniform_overshoots_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_uniform_overshoots_reflInter_eq
  {n : ℕ} :
-- imply
  (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4 > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {0}})).card ≤ (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4 := by
-- proof
  apply StatMech.Walls.rc62_uniform_overshoots_reflInter

/--
[rc62_fixpoint_wall_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_fixpoint_wall_fin2_eq
  {n : ℕ} :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true → (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc62_fixpoint_wall_fin2

/--
[rc62_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc62_reimerWprobCore_of_boxUnionBound h

/--
[rc62_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean)
-/
@[path]
private lemma rc62_status_eq
  {n : ℕ} :
-- imply
  (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧ (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ), (∀ (i : Fin 2) (p : _), Φ (rc62_step i p) = Φ p) → (∀ p, (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) → (∀ p, Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) ∧ ((({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4 > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true → (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc62_status


-- created on 2026-10-23
