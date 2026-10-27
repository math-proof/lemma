import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc86consolidation
open Finset MeasureTheory StatMech StatMech.Walls


/--
[rc86_complete_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc86consolidation.lean)
-/
@[path]
private lemma rc86_complete_chain_eq :
-- imply
  (rc64_ReimerLeaf → rc60_BoxUnionBound) ∧ (rc60_BoxUnionBound → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc60_BoxUnionBound → ReimerWprobCore) ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) ∧ (∀ (_h : ReimerWprobCore) {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)), (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) := by
-- proof
  apply StatMech.Walls.rc86_complete_chain

/--
[rc86_reimer_of_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc86consolidation.lean)
-/
@[path]
private lemma rc86_reimer_of_leaf_eq
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
  apply StatMech.Walls.rc86_reimer_of_leaf h hp A B

/--
[rc86_proved_subclasses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc86consolidation.lean)
-/
@[path]
private lemma rc86_proved_subclasses_eq :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)), (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card → (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card → (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι), (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) := by
-- proof
  apply StatMech.Walls.rc86_proved_subclasses

/--
[rc86_marriage_fraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc86consolidation.lean)
-/
@[path]
private lemma rc86_marriage_fraction_eq :
-- imply
  (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (𝒯 : Finset (Finset (Fin m))), 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ → 𝒯.card ≤ 1 → 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))), ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧ (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card) := by
-- proof
  apply StatMech.Walls.rc86_marriage_fraction

/--
[rc86_refuted_routes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc86consolidation.lean)
-/
@[path]
private lemma rc86_refuted_routes_eq :
-- imply
  (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ), (∀ (i : Fin 2) (p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2))), Φ (rc62_step i p) = Φ p) → (∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)), (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) → (∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)), Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) ∧ (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card / 4 > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card) ∧ (∀ p ∈ rc63_nontrivialPairs, rc63_opGood p.1 p.2 = false) ∧ ((rc73_disjOcc (Down.compression 0 ({∅, {0}, {0, 1}, {2}} : Finset (Finset (Fin 3)))) (rc73_upComp 0 ({∅, {0}, {0, 1}, {0, 2}, {1}, {2}} : Finset (Finset (Fin 3))))).card < (rc73_disjOcc ({∅, {0}, {0, 1}, {2}} : Finset (Finset (Fin 3))) ({∅, {0}, {0, 1}, {0, 2}, {1}, {2}} : Finset (Finset (Fin 3)))).card) ∧ (¬ (rc79_disjOcc3 rc79_rA rc79_rB).card ≤ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card) ∧ ((rc80_reflInterG rc81_wA rc81_wA).card < (rc80_reflInterG (rc81_upClosure rc81_wA) rc81_wA).card) ∧ ((rc80_reflInterG rc82_wA rc82_wA).card < (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card) ∧ (¬ ∃ Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2), (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2), Lc ω₁ ω₂ ∈ rc72_wits rc72_wA rc72_wB ω₁) ∧ (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2), (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ rc72_wA ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ rc72_wB) ∧ Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) => graftSwap (Lc p.1 p.2) p) (rc72_source rc72_wA rc72_wB)) := by
-- proof
  apply StatMech.Walls.rc86_refuted_routes

/--
[rc86_minimal_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc86consolidation.lean)
-/
@[path]
private lemma rc86_minimal_residue_eq :
-- imply
  (rc20_FamCylBoxResidue → ReimerWprobCore) ∧ (rc17_NonMonotoneDeficit → ReimerWprobCore) ∧ (rc64_ReimerLeaf → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc86_minimal_residue

/--
[rc86_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc86consolidation.lean)
-/
@[path]
private lemma rc86_status_eq :
-- imply
  (rc64_ReimerLeaf → rc60_BoxUnionBound) ∧ (rc60_BoxUnionBound → ReimerWprobCore) ∧ (rc60_BoxUnionBound → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (∀ (_h : ReimerWprobCore) {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)), (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧ (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ), (∀ (i : Fin 2) (p : _), Φ (rc62_step i p) = Φ p) → (∀ p, (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) → (∀ p, Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) ∧ (∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B → (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) := by
-- proof
  apply StatMech.Walls.rc86_status


-- created on 2026-10-23
