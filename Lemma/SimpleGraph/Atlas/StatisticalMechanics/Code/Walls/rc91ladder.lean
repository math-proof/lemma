import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc91ladder
open Finset MeasureTheory StatMech StatMech.Walls


/--
[rc91_full_ladder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc91ladder.lean)
-/
@[path]
private lemma rc91_full_ladder_eq :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι), (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (a b : ConfigSpace ι), (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), A ∩ B = ∅ → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc90_ReflCover A B → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), rc90_ComplClosed A → (rc80_disjOccG A A).card ≤ (rc80_reflInterG A A).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)), (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card → (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card → (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) := by
-- proof
  apply StatMech.Walls.rc91_full_ladder

/--
[rc91_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc91ladder.lean)
-/
@[path]
private lemma rc91_chain_eq :
-- imply
  (rc64_ReimerLeaf → rc60_BoxUnionBound) ∧ (rc60_BoxUnionBound → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc60_BoxUnionBound → ReimerWprobCore) ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) ∧ (∀ (_h : ReimerWprobCore) {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)), (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) := by
-- proof
  apply StatMech.Walls.rc91_chain

/--
[rc91_minimal_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc91ladder.lean)
-/
@[path]
private lemma rc91_minimal_residue_eq :
-- imply
  (rc20_FamCylBoxResidue → ReimerWprobCore) ∧ (rc17_NonMonotoneDeficit → ReimerWprobCore) ∧ (rc64_ReimerLeaf → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc91_minimal_residue

/--
[rc91_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc91ladder.lean)
-/
@[path]
private lemma rc91_status_eq :
-- imply
  (rc64_ReimerLeaf → rc60_BoxUnionBound) ∧ (rc60_BoxUnionBound → ReimerWprobCore) ∧ (rc60_BoxUnionBound → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (∀ (_h : ReimerWprobCore) {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)), (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) ∧ ((∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι), (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (a b : ConfigSpace ι), (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), A ∩ B = ∅ → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc90_ReflCover A B → (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), rc90_ComplClosed A → (rc80_disjOccG A A).card ≤ (rc80_reflInterG A A).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)), (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card → (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card → (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card)) ∧ (∀ {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B → (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B) := by
-- proof
  apply StatMech.Walls.rc91_status


-- created on 2026-10-23
