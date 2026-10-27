/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Data.Fin.SkipTwo
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Lemma.Finset.PermFinset
import Macro.LinearAlgebra.Matrix.Determinant.DesnanotJacobi
open Matrix BigOperators Finset

/-!
# Determinants: Factor Hunting and Desnanot-Jacobi Identity

This file formalizes results from the "Factor hunting" and "Desnanot-Jacobi and Dodgson
condensation" sections of the determinants chapter.

## Main definitions

* `vandermondeMat`: The Vandermonde matrix with entries `a i ^ (n - j)`
* `cauchyMat`: The Cauchy matrix with entries `1 / (x i + y j)`

## Main results

### Vandermonde determinant (Theorem thm.det.vander)
* `vandermonde_det_a`: det(aᵢⁿ⁻ʲ) = ∏_{i<j} (aᵢ - aⱼ)
* `vandermonde_det_b`: det(aⱼⁿ⁻ⁱ) = ∏_{i<j} (aᵢ - aⱼ)
* `vandermonde_det_c`: det(aᵢʲ⁻¹) = ∏_{j<i} (aᵢ - aⱼ)
* `vandermonde_det_d`: det(aⱼⁱ⁻¹) = ∏_{j<i} (aᵢ - aⱼ)

### Proposition prop.det.(xi+yj)n-1
* `det_sum_pow`: det((xᵢ + yⱼ)ⁿ⁻¹) = (∏ₖ C(n-1,k)) · (∏_{i<j}(xᵢ-xⱼ)) · (∏_{i<j}(yⱼ-yᵢ))

### Laplace expansion (Theorem thm.det.laplace)
* `det_laplace_row`: det A = ∑_q (-1)^(p+q) A_{p,q} det(A_{~p,~q})
* `det_laplace_col`: det A = ∑_p (-1)^(p+q) A_{p,q} det(A_{~p,~q})

### Proposition prop.det.laplace.0
* `det_laplace_row_zero`: 0 = ∑_q (-1)^(p+q) A_{r,q} det(A_{~p,~q}) when p ≠ r
* `det_laplace_col_zero`: 0 = ∑_p (-1)^(p+q) A_{p,r} det(A_{~p,~q}) when q ≠ r

### Adjugate matrix (Definition def.det.adj, Theorem thm.det.adj.inverse)
* `adjugate`: The adjugate (classical adjoint) of a matrix
* `adjugate_mul`: A · adj(A) = det(A) · I
* `mul_adjugate`: adj(A) · A = det(A) · I

### Desnanot-Jacobi identity (Theorem thm.det.des-jac-1, thm.det.des-jac-2)
* `desnanot_jacobi`: det(A) · det(A') = det(A_{~1,~1}) · det(A_{~n,~n}) - det(A_{~1,~n}) · det(A_{~n,~1})
* `desnanot_jacobi_general`: Generalization with arbitrary rows p,q and columns u,v

### Cauchy determinant (Theorem thm.det.cauchy)
* `cauchy_det`: det(1/(xᵢ+yⱼ)) = ∏_{i<j}((xᵢ-xⱼ)(yᵢ-yⱼ)) / ∏_{i,j}(xᵢ+yⱼ)

### Jacobi's complementary minor theorem (Theorem thm.det.jacobi-complement)
* `jacobi_complementary_minor`: det(sub_P^Q(adj A)) = (-1)^(sum P + sum Q) · (det A)^(|Q|-1) · det(sub_{~Q}^{~P} A)

## References

* Source: DesnanotJacobi.tex (Factor hunting and Desnanot-Jacobi sections)

## Implementation notes

Many of these results are already in Mathlib under `Matrix.det_vandermonde`, `Matrix.adjugate`,
`Matrix.det_laplace_row`, etc. This file provides the statements matching the textbook
presentation and connects them to Mathlib's API.
-/


/-!
## Fin.succAbove computation lemmas

These simp lemmas allow efficient computation of `Fin.succAbove` for concrete Fin types.
They are used throughout this file for determinant expansions involving submatrices.
All lemmas are proved by `rfl` for maximum efficiency.
-/


/-!
## Fin 3 product lemmas

These lemmas simplify products over pairs and singletons in `Fin 3`.
They are used in Cauchy determinant computations for the n = 3 case.
-/


namespace AlgebraicCombinatorics

namespace Determinants

variable {R : Type*} [CommRing R]

variable {n : ℕ}

section SuccAboveLemmas

end SuccAboveLemmas

section Fin3ProductLemmas

variable {R : Type*} [CommMonoid R]

end Fin3ProductLemmas

section ComplementaryMinorInverse

variable {K : Type*} [Field K]

/-! ### Helper lemmas for the Schur complement approach

The key identity for block matrices relates the determinant of the adjugate's top-left block
to the determinant of the original matrix and its bottom-right block:

  det(adj(M).toBlocks₁₁) = det(M)^(k-1) * det(M.toBlocks₂₂)

where k is the size of the top-left block.

This follows from the Schur complement formula for block matrix inverses.
-/

/-- Helper: convert orderIsoOfFin to an embedding from Fin |P| to Fin m.
    This gives an order-preserving embedding that picks out the elements of P. -/
noncomputable def finsetOrderEmb {m : ℕ} (P : Finset (Fin m)) : Fin P.card ↪ Fin m :=
  (P.orderIsoOfFin rfl).toEmbedding.trans (Function.Embedding.subtype _)

/-- Equivalence that sorts indices so that P elements come first (as Sum.inl)
    and Pᶜ elements come second (as Sum.inr). This uses `finSumEquivOfFinset`. -/
noncomputable def sortEquivPQ {m : ℕ} (P : Finset (Fin m)) : Fin P.card ⊕ Fin (m - P.card) ≃ Fin m :=
  finSumEquivOfFinset rfl (by rw [Finset.card_compl, Fintype.card_fin])

/-- Cast version of sortEquivPQ for when we need matching domain types. -/
noncomputable def sortEquivPQ_cast {m : ℕ} (Q : Finset (Fin m)) (k : ℕ) (hk : Q.card = k) : 
    Fin k ⊕ Fin (m - k) ≃ Fin m :=
  (Equiv.sumCongr (finCongr hk.symm) (finCongr (by omega))).trans (sortEquivPQ Q)

end ComplementaryMinorInverse

/-!
### Alternative Approach via Jacobi's Complementary Minor Theorem

The `desnanot_jacobi_direct` lemma below can alternatively be proved using `jacobi_complementary_minor`
(which is already proved in this file). The key insight is:

1. `jacobi_complementary_minor` with P = {u, v} and Q = {p, q} gives:
   `submatrixDet A.adjugate {u,v} {p,q} = (-1)^(u+v+p+q) * A.det * submatrixDet A {p,q}ᶜ {u,v}ᶜ`

2. The LHS can be expressed as a 2×2 determinant of adjugate entries:
   `A.adjugate u p * A.adjugate v q - A.adjugate u q * A.adjugate v p`

3. By `adjugate_2x2_eq`, this equals:
   `(-1)^(p+u+q+v) * (det(A_{~p,~u}) * det(A_{~q,~v}) - det(A_{~q,~u}) * det(A_{~p,~v}))`

4. Combining and canceling the sign factor:
   `det(A_{~p,~u}) * det(A_{~q,~v}) - det(A_{~p,~v}) * det(A_{~q,~u}) = A.det * submatrixDet A {p,q}ᶜ {u,v}ᶜ`

5. The RHS `submatrixDet A {p,q}ᶜ {u,v}ᶜ` equals `(submatrixRemove2 A p q u v).det`, giving the
   Desnanot-Jacobi identity.

This approach requires proving that `orderEmbOfFin` on the complement `{p,q}ᶜ` gives the same
indexing as `skipTwo p q`. The following helper lemmas support this approach.
-/
/-!
## Cauchy Determinant (Theorem thm.det.cauchy)

The Cauchy determinant formula gives the determinant of the matrix (1/(xᵢ + yⱼ)).
-/


/-- The Cauchy matrix with entries 1/(xᵢ + yⱼ).
    Label: thm.det.cauchy -/
def cauchyMat {K : Type*} [Field K] (x y : Fin n → K)
    (_h : ∀ i j, x i + y j ≠ 0) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (x i + y j)⁻¹

/-! ### Helper lemmas for Cauchy determinant -/


/-- The numerator of the Cauchy determinant formula:
    ∏_{i<j}((xᵢ - xⱼ)(yᵢ - yⱼ)) -/
def cauchyNumerator {K : Type*} [Field K] {m : ℕ} (x y : Fin m → K) : K :=
  ∏ i : Fin m, ∏ j ∈ Ioi i, (x i - x j) * (y i - y j)

/-- The denominator of the Cauchy determinant formula:
    ∏_{i,j}(xᵢ + yⱼ) -/
def cauchyDenominator {K : Type*} [Field K] {m : ℕ} (x y : Fin m → K) : K :=
  ∏ i : Fin m, ∏ j : Fin m, (x i + y j)

/-!
### Multivariate Factor Theorem

The multivariate factor theorem is a key tool for the factor hunting proof.
It states that if a polynomial P evaluates to 0 when we substitute X_j for X_i,
then (X_i - X_j) divides P.

This is proved by induction on the polynomial structure, showing that
P - P|_{X_i = X_j} is divisible by (X_i - X_j).
-/


-- Note: cauchy_det is now defined after cauchy_det_of_poly (later in this file)
-- to avoid the forward reference issue.


/-- Substitution that replaces X_i with X_j in a multivariate polynomial. -/
noncomputable def substXiToXj {σ : Type*} [DecidableEq σ] (i j : σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun k => if k = i then MvPolynomial.X j else MvPolynomial.X k)

/-!
## Multivariate Factor Theorem

The multivariate factor theorem states: if P ∈ MvPolynomial σ R (R a domain)
and P evaluates to 0 when we substitute X_j for X_i, then (X_i - X_j) | P.

This is proved by viewing P as a univariate polynomial in X_i over the ring
of polynomials in the other variables, and applying the standard factor theorem.

These lemmas provide the infrastructure needed for the factor hunting proof
of the Cauchy determinant formula.
-/


section FactorTheorem

variable [IsDomain R]

end FactorTheorem

/-!
### Divisibility lemmas for the polynomial Cauchy determinant

These lemmas establish that the determinant of the polynomial Cauchy matrix is divisible
by each factor (x_i - x_j) and (y_i - y_j) for i ≠ j. This is the key step in the
factor hunting proof of the Cauchy determinant formula.
-/


/-- The polynomial Cauchy matrix over MvPolynomial (Fin n ⊕ Fin n) ℤ.
    Entry (i, j) is ∏_{k ≠ j} (X_{inl i} + X_{inr k}). -/
noncomputable def polyCauchyMat' (m : ℕ) : 
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m ⊕ Fin m) ℤ) :=
  Matrix.of fun i j => ∏ k ∈ Finset.univ.filter (· ≠ j), 
    (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr k))

/-- Substitution that sets x_i = x_j (replaces X_{inl i} with X_{inl j}). -/
noncomputable def substX_inl (m : ℕ) (i j : Fin m) : 
    MvPolynomial (Fin m ⊕ Fin m) ℤ →ₐ[ℤ] MvPolynomial (Fin m ⊕ Fin m) ℤ :=
  MvPolynomial.aeval (fun k => 
    if k = Sum.inl i then MvPolynomial.X (Sum.inl j) else MvPolynomial.X k)

/-- Substitution that sets y_i = y_j (replaces X_{inr i} with X_{inr j}). -/
noncomputable def substY_inr (m : ℕ) (i j : Fin m) : 
    MvPolynomial (Fin m ⊕ Fin m) ℤ →ₐ[ℤ] MvPolynomial (Fin m ⊕ Fin m) ℤ :=
  MvPolynomial.aeval (fun k => 
    if k = Sum.inr i then MvPolynomial.X (Sum.inr j) else MvPolynomial.X k)

/-!
### Coprimality of linear factors

To complete the factor hunting proof of the Cauchy determinant, we need to show that
the linear factors (X_i - X_j) and (X_k - X_l) are coprime when they correspond to
different pairs. This section establishes the necessary lemmas.
-/
/-!
### Helper lemmas for the factor hunting proof

The following lemmas establish pairwise coprimality of factors and show that
the product of all factors divides the determinant. This is the key step in
the factor hunting proof of the Cauchy determinant formula.
-/


/-- The set of ordered pairs (i, j) with i < j in Fin m.
    Used to index the linear factors in the Cauchy determinant formula. -/
def orderedPairs' (m : ℕ) : Finset (Σ _ : Fin m, Fin m) :=
  Finset.univ.sigma (fun i : Fin m => Ioi i)

/-- The x-factor for an ordered pair: X_{inl i} - X_{inl j}. -/
noncomputable def xFactor' (m : ℕ) (p : Σ _ : Fin m, Fin m) : 
    MvPolynomial (Fin m ⊕ Fin m) ℤ :=
  MvPolynomial.X (Sum.inl p.1) - MvPolynomial.X (Sum.inl p.2)

/-- The y-factor for an ordered pair: X_{inr i} - X_{inr j}. -/
noncomputable def yFactor' (m : ℕ) (p : Σ _ : Fin m, Fin m) : 
    MvPolynomial (Fin m ⊕ Fin m) ℤ :=
  MvPolynomial.X (Sum.inr p.1) - MvPolynomial.X (Sum.inr p.2)

/-!
### Evaluation equality for the Cauchy determinant

This section proves that at the evaluation point f(inl i) = i, f(inr j) = m + j,
the determinant of the polynomial Cauchy matrix equals the product of squared differences.

This is the key lemma needed to complete the factor hunting proof for the Cauchy determinant.
-/


/-- The evaluated polynomial Cauchy matrix entry at x_i = i, y_j = m + j -/
def evalPolyCauchyEntry (m : ℕ) (i j : Fin m) : ℤ :=
  ∏ k ∈ Finset.univ.filter (· ≠ j), ((i : ℤ) + m + k)

/-- The numerator: ∏_{i<j} (i - j)² -/
def evalNumerator (m : ℕ) : ℤ :=
  ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, ((i : ℤ) - j) * ((i : ℤ) - j)

/-- The Cauchy matrix over ℚ with specific values x_i = i, y_j = m + j -/
noncomputable def cauchyMatEval (m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  Matrix.of fun i j => ((i : ℚ) + m + j)⁻¹

/-- The numerator over ℚ -/
def evalNumeratorQ (m : ℕ) : ℚ :=
  ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, ((i : ℚ) - j) * ((i : ℚ) - j)

/-- The denominator over ℚ -/
def evalDenominatorQ (m : ℕ) : ℚ :=
  ∏ i : Fin m, ∏ j : Fin m, ((i : ℚ) + m + j)

/-- Generalized denominator: ∏_{i,j : Fin n}(i + offset + j) -/
def genDenom (n offset : ℕ) : ℚ :=
  ∏ i : Fin n, ∏ j : Fin n, ((i : ℚ) + offset + j)

/-- Shifted Cauchy matrix: entries are 1/(i + offset + j) -/
noncomputable def cauchyMatEvalShifted (n offset : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => ((i : ℚ) + offset + j)⁻¹

/-- The diagonal matrix over ℚ -/
def evalDiagMat (m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  Matrix.diagonal fun i => ∏ k : Fin m, ((i : ℚ) + m + k)

/-!
### Base cases for shifted Cauchy determinant

These lemmas prove the determinant formula for shifted Cauchy matrices of small sizes.
They are used in the inductive proof of the general Cauchy determinant formula.
-/

/-- Helper to compute the LHS of the Desnanot-Jacobi Cauchy identity -/
def desnanot_jacobi_cauchy_lhs (m : ℕ) : ℚ :=
  evalNumeratorQ (m + 8) / genDenom (m + 8) (m + 8)

/-- Helper to compute the RHS of the Desnanot-Jacobi Cauchy identity -/
def desnanot_jacobi_cauchy_rhs (m : ℕ) : ℚ :=
  let N₆ := evalNumeratorQ (m + 6)
  let N₇ := evalNumeratorQ (m + 7)
  let D_inner := genDenom (m + 6) (m + 10)
  let D₀₀ := genDenom (m + 7) (m + 10)
  let D_LL := genDenom (m + 7) (m + 8)
  let D₀L := genDenom (m + 7) (m + 9)
  (N₇^2 / (D₀₀ * D_LL) - N₇^2 / D₀L^2) * D_inner / N₆

/-- Helper to compute the LHS of the generalized Desnanot-Jacobi Cauchy identity.
    For n ≥ 0 and offset ≥ n + 4:
    LHS = N_{n+4} / D_{n+4,offset} -/
def desnanot_jacobi_cauchy_gen_lhs (n offset : ℕ) : ℚ :=
  evalNumeratorQ (n + 4) / genDenom (n + 4) offset

/-- Helper to compute the RHS of the generalized Desnanot-Jacobi Cauchy identity.
    For n ≥ 0 and offset ≥ n + 4:
    RHS = (N_{n+3}² / (D_{n+3,off+2} * D_{n+3,off}) - N_{n+3}² / D_{n+3,off+1}²) * D_{n+2,off+2} / N_{n+2}
    
    This is derived from Desnanot-Jacobi:
      det(A) · det(inner) = det(A₀₀) · det(A_LL) - det(A₀L)²
    where:
      - det(A) = N_{n+4} / D_{n+4,off}
      - det(inner) = N_{n+2} / D_{n+2,off+2}
      - det(A₀₀) = N_{n+3} / D_{n+3,off+2}
      - det(A_LL) = N_{n+3} / D_{n+3,off}
      - det(A₀L) = N_{n+3} / D_{n+3,off+1} -/
def desnanot_jacobi_cauchy_gen_rhs (n offset : ℕ) : ℚ :=
  let N_inner := evalNumeratorQ (n + 2)
  let N_sub := evalNumeratorQ (n + 3)
  let D_inner := genDenom (n + 2) (offset + 2)
  let D₀₀ := genDenom (n + 3) (offset + 2)
  let D_LL := genDenom (n + 3) offset
  let D₀L := genDenom (n + 3) (offset + 1)
  (N_sub^2 / (D₀₀ * D_LL) - N_sub^2 / D₀L^2) * D_inner / N_inner

/-! ### Additional verified instances for polynomial interpolation

For n=0, the identity is a polynomial identity in offset of degree 36.
To prove by polynomial interpolation, we need 37 verified points.
The following lemmas extend the verified instances. -/
/-! ### Additional verified instances for n ≥ 5

These instances provide additional evidence for the algebraic identity and could
be used in a polynomial interpolation proof. For n=5, the polynomial identity has
degree ~256, so we would need ~257 verified points to use interpolation.
-/
/-! ### Polynomial approach for proving the identity

The key insight is that genDenom n offset can be expressed as an explicit polynomial in offset.
For small n, we can expand the product and use ring to prove the identity.
-/


/-- Explicit polynomial formula for genDenom 2 offset -/
def genDenomPoly2 (x : ℚ) : ℚ := x * (x + 1)^2 * (x + 2)

/-- Explicit polynomial formula for genDenom 3 offset -/
def genDenomPoly3 (x : ℚ) : ℚ := x * (x + 1)^2 * (x + 2)^3 * (x + 3)^2 * (x + 4)

/-- Explicit polynomial formula for genDenom 4 offset -/
def genDenomPoly4 (x : ℚ) : ℚ := x * (x + 1)^2 * (x + 2)^3 * (x + 3)^4 * (x + 4)^3 * (x + 5)^2 * (x + 6)

/-- Explicit polynomial formula for genDenom 5 offset -/
def genDenomPoly5 (x : ℚ) : ℚ := 
  x * (x + 1)^2 * (x + 2)^3 * (x + 3)^4 * (x + 4)^5 * (x + 5)^4 * (x + 6)^3 * (x + 7)^2 * (x + 8)

/-- Explicit polynomial formula for genDenom 6 offset -/
def genDenomPoly6 (x : ℚ) : ℚ := 
  x * (x + 1)^2 * (x + 2)^3 * (x + 3)^4 * (x + 4)^5 * (x + 5)^6 * (x + 6)^5 * (x + 7)^4 * (x + 8)^3 * (x + 9)^2 * (x + 10)

/-- Explicit polynomial formula for genDenom 7 offset -/
def genDenomPoly7 (x : ℚ) : ℚ := 
  x * (x + 1)^2 * (x + 2)^3 * (x + 3)^4 * (x + 4)^5 * (x + 5)^6 * (x + 6)^7 * 
  (x + 7)^6 * (x + 8)^5 * (x + 9)^4 * (x + 10)^3 * (x + 11)^2 * (x + 12)

/-- Explicit polynomial formula for genDenom 8 offset -/
def genDenomPoly8 (x : ℚ) : ℚ := 
  x * (x + 1)^2 * (x + 2)^3 * (x + 3)^4 * (x + 4)^5 * (x + 5)^6 * (x + 6)^7 * (x + 7)^8 *
  (x + 8)^7 * (x + 9)^6 * (x + 10)^5 * (x + 11)^4 * (x + 12)^3 * (x + 13)^2 * (x + 14)

/-!
### Helper lemmas for degree/homogeneity arguments

These lemmas establish that when a polynomial divides another polynomial of the same
homogeneous degree, the quotient must be a constant. This is key to completing the
factor hunting proof for the Cauchy determinant.
-/
/-!
## Jacobi's Complementary Minor Theorem (Theorem thm.det.jacobi-complement)

This is a far-reaching generalization of the Desnanot-Jacobi identity,
relating minors of the adjugate to minors of the original matrix.

For subsets P, Q ⊆ [n] with |P| = |Q| ≥ 1:
  det(sub_P^Q(adj A)) = (-1)^(sum P + sum Q) · (det A)^(|Q|-1) · det(sub_{~Q}^{~P} A)
-/

end Determinants
end AlgebraicCombinatorics
