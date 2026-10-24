/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Shearer.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

namespace MathlibExt.InformationTheory.Shearer

/-!
# Finite Shearer's entropy inequality

For finite alphabet `α`, joint pmf `μ : (Fin n → α) → ℝ` with `μ ≥ 0`,
`∑ μ = 1`, and `k`-cover `C : Finset (Finset (Fin n))` where each
`i : Fin n` lies in at least `k` members, `k * H(X) ≤ ∑_{S∈C} H(X_S)`
with `H = -∑ p log p` and `log 0 = 0`.

Source: F. R. K. Chung, R. L. Graham, P. Frankl, J. B. Shearer,
JCTA 43 (1986), DOI 10.1016/0097-3165(86)90019-1.
-/

/-- S-marginal: sum of `μ x` over those `x` whose restriction to `S` equals `y`. -/
def shearerMarginal {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (μ : (Fin n → α) → ℝ) (S : Finset (Fin n)) (y : ↥S → α) : ℝ :=
  ∑ x : (Fin n → α), if (fun s : ↥S => x s.val) = y then μ x else 0

/-- Full entropy `H(X) = -∑ μ log μ`. -/
noncomputable def shearerFullEntropy {n : ℕ} {α : Type*} [Fintype α]
    (μ : (Fin n → α) → ℝ) : ℝ :=
  -∑ x : (Fin n → α), μ x * Real.log (μ x)

/-- Marginal entropy `H(X_S) = -∑_y P_S(y) log P_S(y)`. -/
noncomputable def shearerMarginalEntropy {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (μ : (Fin n → α) → ℝ) (S : Finset (Fin n)) : ℝ :=
  -∑ y : (↥S → α), shearerMarginal μ S y * Real.log (shearerMarginal μ S y)

/-- Restriction from `A ∪ B` to `A`. -/
private def shearerResL {n : ℕ} {α : Type*} (A B : Finset (Fin n))
    (z : ↥(A ∪ B) → α) : ↥A → α :=
  fun m => z ⟨m.val, Finset.mem_union.mpr (Or.inl m.property)⟩

/-- Restriction from `A ∪ B` to `B`. -/
private def shearerResR {n : ℕ} {α : Type*} (A B : Finset (Fin n))
    (z : ↥(A ∪ B) → α) : ↥B → α :=
  fun m => z ⟨m.val, Finset.mem_union.mpr (Or.inr m.property)⟩

/-- Restriction from `A ∪ B` to `A ∩ B`. -/
private def shearerResI {n : ℕ} {α : Type*} (A B : Finset (Fin n))
    (z : ↥(A ∪ B) → α) : ↥(A ∩ B) → α :=
  fun m => z ⟨m.val, Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp m.property).1)⟩

/-- Restriction from `A` to `A ∩ B`. -/
private def shearerResDL {n : ℕ} {α : Type*} (A B : Finset (Fin n))
    (u : ↥A → α) : ↥(A ∩ B) → α :=
  fun m => u ⟨m.val, (Finset.mem_inter.mp m.property).1⟩

/-- Restriction from `B` to `A ∩ B`. -/
private def shearerResDR {n : ℕ} {α : Type*} (A B : Finset (Fin n))
    (v : ↥B → α) : ↥(A ∩ B) → α :=
  fun m => v ⟨m.val, (Finset.mem_inter.mp m.property).2⟩

/-- Gluing maps on `A`, `B` into a map on `A ∪ B`. -/
private def shearerGlue {n : ℕ} {α : Type*} (A B : Finset (Fin n))
    (u : ↥A → α) (v : ↥B → α) : ↥(A ∪ B) → α :=
  fun s => dite (s.val ∈ A) (fun h => u ⟨s.val, h⟩)
    (fun h => v ⟨s.val, (Finset.mem_union.mp s.property).resolve_left h⟩)

/-- The conditionally-independent coupling used for submodularity. -/
private noncomputable def shearerQ {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (μ : (Fin n → α) → ℝ) (A B : Finset (Fin n)) : (↥(A ∪ B) → α) → ℝ :=
  fun z => if shearerMarginal μ (A ∩ B) (shearerResI A B z) = 0 then 0
    else shearerMarginal μ A (shearerResL A B z) * shearerMarginal μ B (shearerResR A B z)
      / shearerMarginal μ (A ∩ B) (shearerResI A B z)

/-- Prefix sets for the chain rule. -/
private def shearerPrefix (n : ℕ) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < j)
end MathlibExt.InformationTheory.Shearer
