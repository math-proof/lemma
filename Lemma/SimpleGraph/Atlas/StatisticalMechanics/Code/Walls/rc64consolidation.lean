import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc64consolidation
open Finset StatMech StatMech.Walls


/--
[rc64_reimerLeaf_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_reimerLeaf_eq_eq
  {n : ℕ} :
-- imply
  rc64_ReimerLeaf = rc59_IndepHall := by
-- proof
  apply StatMech.Walls.rc64_reimerLeaf_eq

/--
[rc64_reimerLeaf_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_reimerLeaf_iff_eq
  {n : ℕ} :
-- imply
  rc64_ReimerLeaf ↔ ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc64_reimerLeaf_iff

/--
[rc64_boxUnionBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_boxUnionBound_eq_eq
  {n : ℕ} :
-- imply
  rc64_BoxUnionBound = rc60_BoxUnionBound := by
-- proof
  apply StatMech.Walls.rc64_boxUnionBound_eq

/--
[rc64_boxUnionBound_of_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_boxUnionBound_of_leaf_eq
  {n : ℕ}
-- given
  (h : rc64_ReimerLeaf) :
-- imply
  rc64_BoxUnionBound := by
-- proof
  apply StatMech.Walls.rc64_boxUnionBound_of_leaf h

/--
[rc64_wall_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_wall_of_boxUnionBound_eq
  {n : ℕ}
  {m : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin m))}
-- given
  (h : rc64_BoxUnionBound) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc64_wall_of_boxUnionBound h m 𝒜 ℬ

/--
[rc64_famCylBoxResidue_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_famCylBoxResidue_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc64_BoxUnionBound) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc64_famCylBoxResidue_of_boxUnionBound h

/--
[rc64_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc64_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc64_reimerWprobCore_of_boxUnionBound h

/--
[rc64_reimerWprobCore_of_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_reimerWprobCore_of_leaf_eq
  {n : ℕ}
-- given
  (h : rc64_ReimerLeaf) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc64_reimerWprobCore_of_leaf h

/--
[rc64_reimer_inequality_of_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_reimer_inequality_of_leaf_eq
  {n : ℕ}
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc64_ReimerLeaf)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc64_reimer_inequality_of_leaf h hp A B

/--
[rc64_reimer_inequality_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_reimer_inequality_of_boxUnionBound_eq
  {n : ℕ}
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc64_BoxUnionBound)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc64_reimer_inequality_of_boxUnionBound h hp A B

/--
[rc64_all_reductions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_all_reductions_eq
  {n : ℕ} :
-- imply
  (rc64_ReimerLeaf → rc64_BoxUnionBound) ∧ (rc64_BoxUnionBound → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc64_BoxUnionBound → ReimerWprobCore) ∧ (rc64_ReimerLeaf → ReimerWprobCore) ∧ (∀ (_h : ReimerWprobCore) (E : Type) [Fintype E] [DecidableEq E] (p : ℝ≥0) (hp : p ≤ 1) (A B : Set (ConfigSpace E)), (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) := by
-- proof
  apply StatMech.Walls.rc64_all_reductions

/--
[rc64_impossibility_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_impossibility_summary_eq
  {n : ℕ} :
-- imply
  (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ), (∀ (i : Fin 2) (p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2))), Φ (rc62_step i p) = Φ p) → (∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)), (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) → (∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)), Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) ∧ (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card / 4 > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card) ∧ (∀ p ∈ rc63_nontrivialPairs, rc63_opGood p.1 p.2 = false) ∧ ((∅ : Finset (Fin 2)) ∈ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} ∧ (∅ : Finset (Fin 2)) ∉ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}}) ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {∅} ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {{0}} ∧ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} = {{0}} ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} = {∅}) := by
-- proof
  apply StatMech.Walls.rc64_impossibility_summary

/--
[rc64_marriage_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_marriage_empty_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (∅ : Finset (Finset (Fin n))).card ≤ ((∅ : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc64_marriage_empty 𝒜 ℬ

/--
[rc64_marriage_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_marriage_singleton_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  ({S} : Finset (Finset (Fin n))).card ≤ (({S} : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc64_marriage_singleton 𝒜 ℬ hS

/--
[rc64_marriage_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_marriage_card_le_one_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))}
-- given
  (h𝒯 : 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ)
  (hcard : 𝒯.card ≤ 1) :
-- imply
  𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc64_marriage_card_le_one 𝒜 ℬ 𝒯 h𝒯 hcard

/--
[rc64_marriage_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_marriage_fin2_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc64_marriage_fin2 𝒜 ℬ

/--
[rc64_marriage_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_marriage_fin3_refuter_eq
  {n : ℕ} :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card := by
-- proof
  apply StatMech.Walls.rc64_marriage_fin3_refuter

/--
[rc64_marriage_fin3_ex2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_marriage_fin3_ex2_eq
  {n : ℕ} :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox rc64_A3ex2 rc64_B3ex2).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc64_A3ex2 rc64_B3ex2)).card := by
-- proof
  apply StatMech.Walls.rc64_marriage_fin3_ex2

/--
[rc64_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc64consolidation.lean)
-/
@[path]
private lemma rc64_status_eq
  {n : ℕ} :
-- imply
  (rc64_ReimerLeaf → ReimerWprobCore) ∧ (rc64_BoxUnionBound → ReimerWprobCore) ∧ (rc64_ReimerLeaf → rc64_BoxUnionBound) ∧ (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (𝒯 : Finset (Finset (Fin m))), 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ → 𝒯.card ≤ 1 → 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))), ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧ (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card) ∧ (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ), (∀ (i : Fin 2) (p : _), Φ (rc62_step i p) = Φ p) → (∀ p, (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) → (∀ p, Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) := by
-- proof
  apply StatMech.Walls.rc64_status


-- created on 2026-10-23
