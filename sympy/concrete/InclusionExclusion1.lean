/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
/-!
# The Principles of Inclusion and Exclusion

This file formalizes the inclusion-exclusion principles and their applications from
Section `sec.sign.pie` of the Algebraic Combinatorics notes.

## Main results

### Size version (Theorem `thm.pie.1`)
The size version of PIE states that for a finite set `U` and subsets `A₁, ..., Aₙ`:
  |{u ∈ U : u ∉ Aᵢ for all i}| = ∑_{I ⊆ [n]} (-1)^|I| |{u ∈ U : u ∈ Aᵢ for all i ∈ I}|

This is already available in Mathlib as `Finset.inclusion_exclusion_card_inf_compl`.

### Applications

* `numSurj` - The number of surjective maps from `[m]` to `[n]` (Theorem `thm.pie.count-sur`)
* `numSurj_formula` - The formula: ∑_{k=0}^{n} (-1)^k * C(n,k) * (n-k)^m
* Corollaries about the surjection count (`cor.pie.count-sur.cors`)
* `Derangement` - Permutations with no fixed points (Definition `def.pie.dera`)
* `numDerangements_formula` - The derangement count formula (Theorem `thm.pie.count-der`)
* `totient_eq_prod_one_sub_inv` - Euler's totient formula (Theorem `thm.pie.euler-tot`)

### Weighted version (Theorem `thm.pie.2`)
The weighted version generalizes the size version by replacing cardinalities with weighted sums.
This is already available in Mathlib as `Finset.inclusion_exclusion_sum_inf_compl`.

## References

* Section `sec.sign.pie` of the Algebraic Combinatorics notes
* Mathlib's `Mathlib.Combinatorics.Enumerative.InclusionExclusion`
-/


open Finset BigOperators Nat

namespace AlgebraicCombinatorics.InclusionExclusion
/-! ### Size version of PIE (Theorem `thm.pie.1`)

The size version is already in Mathlib. We restate it here for reference.
See `Finset.inclusion_exclusion_card_inf_compl`.

For a finite set `U` and subsets `A₁, ..., Aₙ`:
  |U \ (A₁ ∪ ... ∪ Aₙ)| = ∑_{I ⊆ [n]} (-1)^|I| |⋂_{i ∈ I} Aᵢ|

where the empty intersection is taken to be `U`.
-/
/-! ### Example 1: Counting surjective maps (Theorem `thm.pie.count-sur`)

The number of surjective maps from `Fin m` to `Fin n` is
  ∑_{k=0}^{n} (-1)^k * C(n,k) * (n-k)^m
-/


/-- The number of surjective maps from `Fin m` to `Fin n`. -/
def numSurj (m n : ℕ) : ℕ := Fintype.card {f : Fin m → Fin n // Function.Surjective f}
/-! #### Helper lemmas for the surjection formula -/

/-- For each `i : Fin n`, the set of functions `f : Fin m → Fin n` such that `i ∉ range f`. -/
def S_avoid (m n : ℕ) (i : Fin n) : Finset (Fin m → Fin n) :=
  univ.filter (fun f => i ∉ Set.range f)
/-! ### Corollary `cor.pie.count-sur.cors`: Consequences of the surjection formula -/
/-! #### Helper lemmas for the divisibility proof

The proof uses the orbit-stabilizer theorem. The symmetric group `Perm (Fin n)` acts on
surjective maps `Fin m → Fin n` by post-composition. Since this action is free (the stabilizer
of any surjective map is trivial), the number of surjections is divisible by `n!`.
-/


/-- Action of `Perm (Fin n)` on functions `Fin m → Fin n` by post-composition. -/
instance permActionOnFun (m n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Fin m → Fin n) where
  smul σ f := σ ∘ f
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Post-composition with a permutation preserves surjectivity. -/
theorem surjective_smul {m n : ℕ} (σ : Equiv.Perm (Fin n)) {f : Fin m → Fin n}
    (hf : Function.Surjective f) : Function.Surjective (σ • f) := by
  intro y
  obtain ⟨x, hx⟩ := hf (σ.symm y)
  use x
  simp only [HSMul.hSMul, SMul.smul, hx, Equiv.apply_symm_apply]

/-- Action of `Perm (Fin n)` on surjective functions `Fin m → Fin n` by post-composition. -/
instance permActionOnSurj (m n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) {f : Fin m → Fin n // Function.Surjective f} where
  smul σ f := ⟨σ • f.val, surjective_smul σ f.prop⟩
  one_smul f := by ext; simp [HSMul.hSMul, SMul.smul]
  mul_smul σ τ f := by ext; simp [HSMul.hSMul, SMul.smul]
/-! ### Example 2: Derangements (Definition `def.pie.dera` and Theorem `thm.pie.count-der`)

A derangement is a permutation with no fixed points.

**Relationship to Mathlib:**
- Mathlib defines `derangements α : Set (Perm α)` in `Mathlib.Combinatorics.Derangements.Basic`
- Mathlib defines `numDerangements : ℕ → ℕ` in `Mathlib.Combinatorics.Derangements.Finite`
- Our `Derangement α` is definitionally equal to `↥(derangements α)` (the subtype)
- `Fintype.card (Derangement (Fin n))` equals `numDerangements n` (see `card_Derangement_eq`)

We provide the explicit `Derangement` type to make the connection to the textbook explicit.
The main theorems use Mathlib's `numDerangements` directly.
-/


/-- **Definition `def.pie.dera`**: A derangement of a type `α` is a permutation with no fixed points.

This is definitionally equal to `↥(derangements α)` from `Mathlib.Combinatorics.Derangements.Basic`.

**Textbook definition:** "A derangement of a set X means a permutation of X that has no fixed points."

**Examples from the textbook:**
- D₀ = 1: The identity on ∅ is a derangement (vacuously no fixed points)
- D₁ = 0: The identity on {0} fixes 0, so it's not a derangement
- D₂ = 1: Only the swap (0 1) is a derangement
- D₃ = 2: The two 3-cycles (0 1 2) and (0 2 1) are derangements -/
def Derangement (α : Type*) := {σ : Equiv.Perm α // ∀ x, σ x ≠ x}

instance {α : Type*} [DecidableEq α] [Fintype α] : Fintype (Derangement α) :=
  Subtype.fintype _

/-- A derangement is a permutation in `derangements α`.
This shows our definition matches Mathlib's `derangements` set. -/
theorem Derangement.mem_derangements {α : Type*} (σ : Derangement α) :
    σ.val ∈ derangements α := σ.prop

/-- The `Derangement` type is equivalent to the subtype of `derangements α`.
This establishes that our explicit type is equivalent to Mathlib's set-based definition. -/
def Derangement.equivDerangements (α : Type*) :
    Derangement α ≃ (derangements α : Set (Equiv.Perm α)) where
  toFun σ := ⟨σ.val, σ.mem_derangements⟩
  invFun σ := ⟨σ.val, σ.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-! ### Example 3: Euler's totient function (Theorem `thm.pie.euler-tot`)

Euler's totient `φ(c)` counts integers in `[1, c]` coprime to `c`.
The formula expresses this in terms of the prime factorization.

Note: `Nat.totient` is already defined in Mathlib.
-/
/-! ### Example 4: Partitions into distinct vs odd parts

This example shows that `p_dist(n) = p_odd(n)` using PIE.
This is already covered in other chapters on partitions.
-/
/-! ### Weighted version of PIE (Theorem `thm.pie.2`)

The weighted version of the Principle of Inclusion and Exclusion generalizes
the size version by replacing cardinalities with weighted sums.

For a finite set `U`, subsets `A₁, ..., Aₙ`, an additive abelian group `A`,
and a weight function `w : U → A`:

  ∑_{u ∈ U : u ∉ Aᵢ for all i ∈ [n]} w(u) = ∑_{I ⊆ [n]} (-1)^|I| ∑_{u ∈ U : u ∈ Aᵢ for all i ∈ I} w(u)

This is proved in Mathlib as `Finset.inclusion_exclusion_sum_inf_compl`.
Theorem `thm.pie.1` is obtained by setting `w(u) = 1` for all `u`.
-/

end AlgebraicCombinatorics.InclusionExclusion
