/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Theorem.Combinatorics.Young.LittlewoodRichardson.Part4
open Finset Function BigOperators Polynomial MvPolynomial

/-!
# The Littlewood-Richardson Rule

This file formalizes the Littlewood-Richardson rule for Schur polynomials, following
the presentation in the Algebraic Combinatorics textbook.

The Littlewood-Richardson rule is one of the most famous results in the theory of symmetric
polynomials. It provides a combinatorial formula for expanding the product of Schur polynomials
as a sum of Schur polynomials:
$$s_\nu \cdot s_{\lambda/\mu} = \sum_{T} s_{\nu + \operatorname{cont}(T)}$$
where the sum is over all ν-Yamanouchi semistandard tableaux T of shape λ/μ.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of natural numbers
* `contentTableau`: The content of a tableau (counting occurrences of each entry)
* `colGeq`: Restriction of a tableau to columns ≥ j
* `IsYamanouchi`: A semistandard tableau is ν-Yamanouchi if certain conditions hold
* `alternant`: The alternant polynomial a_α
* `schurPoly`: The Schur polynomial s_λ (via the Jacobi-Trudi formula)
* `skewSchurPoly`: The skew Schur polynomial s_{λ/μ}

## Main results

* `littlewoodRichardson`: Zelevinsky's generalized Littlewood-Richardson rule (thm.sf.lr-zy)
* `stembridgeLemma`: Stembridge's lemma (lem.sf.stemb-lem)
* `schurPoly_eq_alternant_div`: Theorem relating Schur polynomials to alternants (thm.sf.schur-symm (b))

## Indexing Convention

**This file uses 1-indexed columns** for skew Young diagrams, matching the textbook convention:
- A cell (i, j) is in Y(λ/μ) iff μ_i < j ≤ λ_i
- Column indices start at 1 (the first column is j = 1)

This differs from `SchurBasics.lean` which uses **0-indexed columns** (Mathlib convention):
- A cell (i, j) is in Y(λ/μ) iff μ_i ≤ j < λ_i
- Column indices start at 0 (the first column is j = 0)

The bijection (i, j) ↔ (i, j+1) converts between the conventions.
See `SchurBasics.skewCellEquiv` and `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted`
for explicit equivalences.

## References

* [Stembridge, *A concise proof of the Littlewood-Richardson rule*][Stembr02]
* [Grinberg-Reiner, *Hopf algebras in Combinatorics*][GriRei]

## Tags

Littlewood-Richardson rule, Schur polynomial, Yamanouchi tableau, symmetric polynomial
-/


namespace AlgebraicCombinatorics

variable {R : Type*} [CommRing R]

variable {N : ℕ}

/-- The type of cells in the skew diagram with column ≥ 1 is equivalent to the full diagram. -/
noncomputable def skewDiagramColGeqOneEquiv (lam mu : Fin N → ℕ) :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1} ≃
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} where
  toFun c := ⟨c.val, c.prop.1⟩
  invFun c := ⟨c.val, c.prop, skewYoungDiagram_col_ge_one c.val c.prop⟩
  left_inv c := by simp
  right_inv c := by simp

/-- Equivalence between cells with entry i in col_{≥1} and all cells with entry i. -/
noncomputable def contentColGeqOneEquiv {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) :
    {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1} // T ⟨c.val, c.prop.1⟩ = i} ≃
    {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T c = i} where
  toFun c := ⟨⟨c.val.val, c.val.prop.1⟩, c.prop⟩
  invFun c := ⟨⟨c.val.val, c.val.prop, skewYoungDiagram_col_ge_one c.val.val c.val.prop⟩, c.prop⟩
  left_inv c := by simp
  right_inv c := by simp

/-! ## Voting metaphor for Yamanouchi condition

The Yamanouchi condition can be understood through a voting metaphor (rmk.sf.yamanouchi.votes):
- Each entry i in T is a vote for candidate i
- We count votes column by column, from right to left
- Starting with tally ν, after processing each column, the tally must remain weakly decreasing
- Key observation: no candidate gains more than one vote at a time (since columns have distinct entries)
-/
/-! ## Alternants and Schur polynomials -/


/-- The alternant a_α = ∑_{σ ∈ S_N} sign(σ) · x^(σ·α).
    Here σ·α means (α_{σ(1)}, α_{σ(2)}, ..., α_{σ(N)}).

    **Equivalence with SchurBasics.alternant:**
    This sum-based definition equals the determinant-based definition in
    `alternant` (from SchurBasics.lean). See `alternant_eq_det` for the proof
    that this equals `det(alternantMatrix α)`. -/
noncomputable def alternant (α : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • xPow (α ∘ σ)

/-- The Vandermonde determinant: a_ρ = ∏_{i<j} (xᵢ - xⱼ).
    (eq.def.sf.alternants.arho=vdm) -/
noncomputable def vandermonde : MvPolynomial (Fin N) R :=
  ∏ i : Fin N, ∏ j : Fin N, if i < j then X i - X j else 1

/-! ### Helper lemmas for alternant_rho_eq_vandermonde -/

/-- Matrix whose determinant equals the alternant.
    Entry (i, j) is x_j^{α_i}. -/
noncomputable def alternantMatrix (α : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R) :=
  Matrix.of fun i j => X j ^ (α i)

/-! ## Regular elements and cancellation

This section formalizes Definition def.cring.reg from the source material.

### Definition (def.cring.reg)

Let L be a commutative ring. Let a ∈ L. The element a of L is said to be **regular**
if and only if every x ∈ L satisfying ax = 0 satisfies x = 0.

Regular elements are also called "non-zero-divisors" or "cancellable" elements.

### Connection to Mathlib

In Mathlib, the relevant concepts are:
- `IsLeftRegular a`: left multiplication by `a` is injective (i.e., `a * x = a * y → x = y`)
- `IsRightRegular a`: right multiplication by `a` is injective
- `IsRegular a`: both left and right regular

The textbook definition (ax = 0 → x = 0) is equivalent to `IsLeftRegular` in any ring.
In a commutative ring, `IsLeftRegular` and `IsRightRegular` are equivalent, so
`IsRegular` is equivalent to either one.

The key equivalence is `isLeftRegular_iff_right_eq_zero_of_mul` from Mathlib:
  `IsLeftRegular r ↔ ∀ x, r * x = 0 → x = 0`
-/


section RegularElements

variable {L : Type*} [CommRing L]

/-- **Definition (def.cring.reg)**: An element `a` of a commutative ring `L` is **regular**
    if and only if every `x ∈ L` satisfying `a * x = 0` satisfies `x = 0`.

    This is the textbook definition. We show it's equivalent to Mathlib's `IsLeftRegular`.
    In commutative rings, this is also equivalent to `IsRegular` and `IsRightRegular`. -/
def IsRegularElement (a : L) : Prop := ∀ x : L, a * x = 0 → x = 0

end RegularElements

/-! ## Schur polynomials -/


/-- The monomial x_T = ∏_i x_i^(# of i's in T) for a tableau T.
    By definition, this equals x^(cont(T)). -/
noncomputable def monomialTableau {lam mu : Fin N → ℕ} (T : Tableau lam mu) :
    MvPolynomial (Fin N) R :=
  xPow (contentTableau T)

end AlgebraicCombinatorics
