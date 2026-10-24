/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.matrices.determinants.PermFinset

set_option backward.isDefEq.respectTransparency false
/-!
# Determinants: Cauchy-Binet and Related Formulas

This file formalizes the Cauchy-Binet formula and related determinant identities,
following Section "Cauchy--Binet ... Factoring the matrix" of the source
(CauchyBinet.tex).

## Main definitions

* `Matrix.submatrix` - The submatrix obtained by restricting to specific rows and columns.
  This corresponds to `sub_U^V A` in the source (Definition def.det.sub).
* `colsSubmatrix`, `rowsSubmatrix` - Submatrices selecting specific columns/rows.

## Main results

* `cauchyBinet` - The general Cauchy-Binet formula for det(AB) where A is n×m and B is m×n
  (Theorem thm.det.CB)
* `cauchyBinet_square` - Special case for square matrices: det(AB) = det(A)·det(B)
* `det_mul_eq_zero_of_rank_deficient` - When m < n, det(AB) = 0
* `det_add_sum` - Formula for det(A+B) as a double sum over subsets (Theorem thm.det.det(A+B))
* `det_diagonal_submatrix_eq`, `det_diagonal_submatrix_off_diag` - Minors of diagonal matrices
  (Lemma lem.det.minors-diag)
* `det_add_diagonal` - Simplified formula when adding a diagonal matrix (Theorem thm.det.det(A+D))
* `det_const_add_diagonal` - Determinant of x + D where D is diagonal (Proposition prop.det.x+ai)
* `det_charPoly_coeff` - Coefficients of the characteristic polynomial
  (Proposition prop.det.charpol-explicit)
* `det_pascal_matrix` - The Pascal matrix has determinant 1 (Proposition prop.det.pascal-LU)

## References

* Source: CauchyBinet.tex

## Implementation notes

Mathlib already provides `Matrix.det_mul` in `Mathlib.LinearAlgebra.Matrix.Determinant`.
We provide additional results and connect Mathlib's API to the textbook presentation.

The submatrix operation `Matrix.submatrix` uses functions for row/column selection,
which is more general than the textbook's subset-based notation.
-/


open scoped Matrix BigOperators
open Finset Matrix

namespace AlgebraicCombinatorics

namespace CauchyBinet

variable {R : Type*} [CommRing R]
/-!
## Submatrices (Definition def.det.sub)

For an n×m matrix A, subsets U ⊆ [n] and V ⊆ [m], we define
sub_U^V A to be the |U|×|V| submatrix obtained by keeping only
the rows indexed by U and columns indexed by V (in increasing order).

In Mathlib, this is `Matrix.submatrix A f g` where f and g are the
order-preserving embeddings of U and V into [n] and [m].
-/


/-- The submatrix of A obtained by restricting to rows in U and columns in V.
    This corresponds to `sub_U^V A` in the source (Definition def.det.sub).
    Label: def.det.sub
    
    ## Mathematical Description
    
    Let A be an n×m matrix. Let U ⊆ [n] and V ⊆ [m] be subsets.
    Writing U = {u₁, u₂, ..., uₚ} with u₁ < u₂ < ... < uₚ
    and V = {v₁, v₂, ..., vₚ} with v₁ < v₂ < ... < vₚ,
    we define sub_U^V A := (A_{uᵢ,vⱼ})_{1≤i≤p, 1≤j≤q}.
    
    This is the |U|×|V| matrix obtained from A by keeping only the rows
    indexed by U and columns indexed by V, in increasing order.
    
    ## Terminology
    
    - **Submatrix**: The matrix sub_U^V A
    - **Minor**: When |U| = |V|, the determinant det(sub_U^V A) is called a minor of A
    - **Principal minor**: When U = V, the minor det(sub_U^U A) is called a principal minor
    
    ## Implementation
    
    In Mathlib, `Matrix.submatrix` takes functions for row and column selection.
    For finite sets, we use the canonical order-preserving embedding `orderEmbOfFin`. -/
noncomputable def submatrixOfFinset {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) :
    Matrix (Fin U.card) (Fin V.card) R :=
  A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin rfl)

/-- Notation for submatrices: `sub[U,V] A` denotes sub_U^V A. -/
scoped notation "sub[" U "," V "] " A => submatrixOfFinset A U V

/-- A **minor** of a matrix A is the determinant of a square submatrix.
    This is det(sub_U^V A) where |U| = |V|.
    
    If |U| ≠ |V|, we define the minor to be 0 (since the submatrix is not square). -/
noncomputable def minor {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) : R :=
  if h : U.card = V.card then
    (A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin (h ▸ rfl))).det
  else 0

/-- A **principal minor** of a square matrix is a minor where U = V.
    These are the determinants of principal submatrices (same rows and columns). -/
noncomputable def principalMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P : Finset (Fin n)) : R :=
  (A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det

/-- Example: For a 3×3 matrix, sub_{0,1}^{0,2} A extracts the 2×2 submatrix
    with rows 0,1 and columns 0,2.
    
    For the matrix:
      (a   b   c  )
      (a'  b'  c' )
      (a'' b'' c'')
    
    we get sub_{0,1}^{0,2} A = (a   c )
                               (a'  c')
    
    Note: The textbook uses 1-indexing, so sub_{1,2}^{1,3} in the textbook
    corresponds to sub_{0,1}^{0,2} in our 0-indexed formalization. -/
example {A : Matrix (Fin 3) (Fin 3) R} :
    let U : Finset (Fin 3) := {0, 1}
    let V : Finset (Fin 3) := {0, 2}
    submatrixOfFinset A U V = A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin rfl) := rfl
/-!
## Cauchy-Binet Formula (Theorem thm.det.CB)

For an n×m matrix A and an m×n matrix B:
  det(AB) = ∑_{g : strictly increasing n-tuple from [m]} det(cols_g A) · det(rows_g B)

This generalizes det(AB) = det(A)·det(B) for square matrices.

Special cases:
- If m < n, the sum is empty, so det(AB) = 0
- If m = n, there's only one term: det(A)·det(B)
-/

/-- Submatrix obtained by selecting specific columns of A.
    `cols_g A` in the source notation selects columns indexed by g. -/
noncomputable def colsSubmatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  A.submatrix id (S.orderEmbOfFin hcard)

/-- Submatrix obtained by selecting specific rows of B.
    `rows_g B` in the source notation selects rows indexed by g. -/
noncomputable def rowsSubmatrix {n m : ℕ} (B : Matrix (Fin m) (Fin n) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  B.submatrix (S.orderEmbOfFin hcard) id
/-!
## Determinant of A + B (Theorem thm.det.det(A+B))

For n×n matrices A and B:
  det(A+B) = ∑_{P ⊆ [n]} ∑_{Q ⊆ [n], |P|=|Q|} (-1)^(sum P + sum Q) · det(sub_P^Q A) · det(sub_P̃^Q̃ B)

where P̃ denotes the complement [n] \ P.

This is a "binomial theorem" for determinants, containing det(A) (P=Q=[n])
and det(B) (P=Q=∅) as special terms.
-/


/-- Sum of elements in a finset of Fin n, viewed as natural numbers.
    Used in the sign factor of the det(A+B) formula.

    Note: This is named `finsetSumFin` to distinguish from `AlgebraicCombinatorics.QBinomialRec.finsetSumNat`,
    which computes the sum of elements in a `Finset ℕ` directly.
    Both compute "the sum of elements" but for different element types. -/
def finsetSumFin {n : ℕ} (P : Finset (Fin n)) : ℕ := ∑ i ∈ P, i.val

/-- Helper: Given P, Q with same cardinality, compute the determinant of the
    submatrix of A restricted to rows P and columns Q. -/
noncomputable def submatrixDet {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card = Q.card) : R :=
  (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det
/-! ### Proof infrastructure for det(A+B) formula

The proof proceeds in several steps:
1. Expand det(A+B) using the Leibniz formula
2. Use the product rule ∏(a+b) = ∑_P (∏_{i∈P} a_i)(∏_{i∈Pᶜ} b_i)
3. Swap the order of summation
4. Partition the sum over σ based on σ(P) = Q
5. Factor out the sign and show it equals (-1)^(sum P + sum Q)
6. Recognize the remaining sums as determinants of submatrices
-/
/-!
### Permutation image definitions

These are local definitions that duplicate the bodies of the canonical definitions in 
`PermFinset` namespace (`Determinants/PermFinset.lean`). The definitions are 
**definitionally equal** to their `PermFinset` counterparts (witnessed by 
`imageFinset_eq_permFinset` and `permsMapping_eq_permFinset`), but are kept as 
separate `def`s rather than wrappers because many proofs in this file rely on 
specific unfolding behavior with `simp [imageFinset]`.

**For new code**: Use `PermFinset.imageFinset` and `PermFinset.permsMapping` directly.
-/


/-- The image of a finset under a permutation.
    
    This is definitionally equal to `PermFinset.imageFinset` (see `imageFinset_eq_permFinset`).
    New code should prefer `PermFinset.imageFinset`. -/
def imageFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  P.map ⟨σ, σ.injective⟩

/-- The set of permutations that map P to Q.
    
    This is definitionally equal to `PermFinset.permsMapping` (see `permsMapping_eq_permFinset`).
    New code should prefer `PermFinset.permsMapping`. -/
def permsMapping {n : ℕ} (P Q : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => imageFinset σ P = Q)
/-! ### Helper lemmas for the key factorization

The proof of `sum_perms_mapping_eq_det_product` requires:
1. A bijection between {σ : σ(P) = Q} and Perm(Fin |P|) × Perm(Fin |Pᶜ|)
2. A sign identity: sign(σ) = (-1)^(sum P + sum Q) · sign(α) · sign(β)
3. Product factorization into determinants

We build these up step by step.
-/


/-- For σ with σ(P) = Q, the image of any element of P under σ lies in Q. -/
theorem sigma_orderEmb_mem_of_imageFinset {n : ℕ} (P Q : Finset (Fin n)) 
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) (i : Fin P.card) :
    σ (P.orderEmbOfFin rfl i) ∈ Q := by
  rw [← hσ]
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
  exact ⟨P.orderEmbOfFin rfl i, Finset.orderEmbOfFin_mem P rfl i, rfl⟩

/-- For σ with σ(P) = Q, the image of any element of Pᶜ under σ lies in Qᶜ. -/
theorem sigma_orderEmb_compl_mem_of_imageFinset {n : ℕ} (P Q : Finset (Fin n)) 
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) (i : Fin Pᶜ.card) :
    σ (Pᶜ.orderEmbOfFin rfl i) ∈ Qᶜ := by
  simp only [Finset.mem_compl]
  intro hcontra
  rw [← hσ] at hcontra
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hcontra
  obtain ⟨p, hp, hσp⟩ := hcontra
  have : Pᶜ.orderEmbOfFin rfl i ∈ P := by
    have h := σ.injective hσp
    rw [← h]
    exact hp
  have hmem : Pᶜ.orderEmbOfFin rfl i ∈ Pᶜ := Finset.orderEmbOfFin_mem Pᶜ rfl i
  exact (Finset.mem_compl.mp hmem) this

/-- Extract α from σ: For σ with σ(P) = Q, extract the permutation α ∈ Perm(Fin |P|)
    that describes how σ permutes the elements of P.
    
    Specifically, if p₁ < p₂ < ... < pₖ are the elements of P and 
    q₁ < q₂ < ... < qₖ are the elements of Q, then α is defined by
    σ(pᵢ) = q_{α(i)}. -/
noncomputable def extractAlpha {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) : Equiv.Perm (Fin P.card) := by
  let pEmb := P.orderEmbOfFin rfl
  have h : ∀ i : Fin P.card, σ (pEmb i) ∈ Q := sigma_orderEmb_mem_of_imageFinset P Q σ hσ
  let qIso : Fin P.card ≃o Q := Q.orderIsoOfFin hcard.symm
  let f : Fin P.card → Fin P.card := fun i => qIso.symm ⟨σ (pEmb i), h i⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    have := qIso.symm.injective hab
    simp only [Subtype.mk.injEq] at this
    exact pEmb.injective (σ.injective this)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- Extract β from σ: For σ with σ(P) = Q, extract the permutation β ∈ Perm(Fin |Pᶜ|)
    that describes how σ permutes the elements of Pᶜ. -/
noncomputable def extractBeta {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) : Equiv.Perm (Fin Pᶜ.card) := by
  have hcard' : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
  let pEmb := Pᶜ.orderEmbOfFin rfl
  have h : ∀ i : Fin Pᶜ.card, σ (pEmb i) ∈ Qᶜ := sigma_orderEmb_compl_mem_of_imageFinset P Q σ hσ
  let qIso : Fin Pᶜ.card ≃o (Qᶜ : Finset (Fin n)) := Qᶜ.orderIsoOfFin hcard'.symm
  let f : Fin Pᶜ.card → Fin Pᶜ.card := fun i => qIso.symm ⟨σ (pEmb i), h i⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    have := qIso.symm.injective hab
    simp only [Subtype.mk.injEq] at this
    exact pEmb.injective (σ.injective this)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
/-! ### Helper lemmas for empty set case in sign_decomposition -/

/-- Given α ∈ Perm(Fin |P|) and β ∈ Perm(Fin |Pᶜ|), construct σ ∈ Perm(Fin n) with σ(P) = Q.
    This is the inverse of the (extractAlpha, extractBeta) bijection. -/
noncomputable def constructSigma {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (α : Equiv.Perm (Fin P.card)) (β : Equiv.Perm (Fin Pᶜ.card)) : Equiv.Perm (Fin n) := by
  have hcardC : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
  let pEmb := P.orderEmbOfFin rfl
  let qEmb : Fin P.card ↪o Fin n := Q.orderEmbOfFin (by rw [hcard])
  let pCEmb := Pᶜ.orderEmbOfFin rfl
  let qCEmb : Fin Pᶜ.card ↪o Fin n := Qᶜ.orderEmbOfFin (by rw [hcardC])
  -- Construct the function
  let f : Fin n → Fin n := fun x =>
    if h : x ∈ P then
      qEmb (α ((P.orderIsoOfFin rfl).symm ⟨x, h⟩))
    else
      qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨x, Finset.mem_compl.mpr h⟩))
  -- Prove it's a bijection
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    by_cases ha : a ∈ P <;> by_cases hb : b ∈ P
    · simp only [ha, hb, dif_pos] at hab
      have := qEmb.injective hab
      have := α.injective this
      have := (P.orderIsoOfFin rfl).symm.injective this
      simp only [Subtype.mk.injEq] at this
      exact this
    · simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true] at hab
      have h1 : qEmb (α ((P.orderIsoOfFin rfl).symm ⟨a, ha⟩)) ∈ Q := Finset.orderEmbOfFin_mem _ _ _
      have h2 : qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨b, Finset.mem_compl.mpr hb⟩)) ∈ Qᶜ := 
        Finset.orderEmbOfFin_mem _ _ _
      rw [hab] at h1
      exact absurd h1 (Finset.mem_compl.mp h2)
    · simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true] at hab
      have h1 : qEmb (α ((P.orderIsoOfFin rfl).symm ⟨b, hb⟩)) ∈ Q := Finset.orderEmbOfFin_mem _ _ _
      have h2 : qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨a, Finset.mem_compl.mpr ha⟩)) ∈ Qᶜ := 
        Finset.orderEmbOfFin_mem _ _ _
      rw [← hab] at h1
      exact absurd h1 (Finset.mem_compl.mp h2)
    · simp only [ha, hb, dif_neg, not_false_eq_true] at hab
      have := qCEmb.injective hab
      have := β.injective this
      have := (Pᶜ.orderIsoOfFin rfl).symm.injective this
      simp only [Subtype.mk.injEq] at this
      exact this
  exact Equiv.ofBijective f ⟨hf_inj, Finite.injective_iff_surjective.mp hf_inj⟩
/-! ### Base case lemmas for sign decomposition using subtypePerm

When P = Q = {0, 1, ..., k-1} (the first k elements), the sign identity simplifies
because inversions split cleanly into three categories:
1. Inversions within P (counted by α)
2. Inversions within Pᶜ (counted by β)  
3. Inversions between P and Pᶜ (which are zero because σ preserves both sets)

We formalize this using Mathlib's `sign_subtypeCongr` lemma and `Equiv.Perm.subtypePerm`.
-/


/-- Predicate for "i.val < k" used to partition Fin n. -/
def ltPred (n k : ℕ) : Fin n → Prop := fun i => i.val < k

instance instDecidablePredLtPred (n k : ℕ) : DecidablePred (ltPred n k) := 
  fun i => Nat.decLt i.val k

/-- A permutation "preserves [k]" if it maps elements with index < k to elements with index < k. -/
def preservesPrefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∀ i : Fin n, i.val < k ↔ (σ i).val < k

/-- Restriction of a permutation to {i | i.val < k} using Mathlib's `subtypePerm`. -/
noncomputable def restrictToLt {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hσ : preservesPrefix σ k) : Equiv.Perm {i : Fin n // ltPred n k i} :=
  σ.subtypePerm fun i => by
    simp only [ltPred]
    exact (hσ i).symm

/-- Restriction of a permutation to {i | i.val ≥ k} using Mathlib's `subtypePerm`. -/
noncomputable def restrictToGe {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hσ : preservesPrefix σ k) : Equiv.Perm {i : Fin n // ¬ltPred n k i} :=
  σ.subtypePerm fun i => by
    simp only [ltPred, not_lt]
    constructor
    · intro h
      exact Nat.le_of_not_lt fun hc => Nat.not_lt.mpr h ((hσ i).mp hc)
    · intro h
      exact Nat.le_of_not_lt fun hc => Nat.not_lt.mpr h ((hσ i).mpr hc)

/-- The finset {0, 1, ..., k-1} ⊆ Fin n. -/
def prefixFinset (n k : ℕ) (_hk : k ≤ n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k)

/-- Equivalence between Fin k and the subtype {i : Fin n // i.val < k}. -/
noncomputable def finEquivSubtypeLt (n k : ℕ) (hk : k ≤ n) : 
    Fin k ≃ {i : Fin n // ltPred n k i} := by
  refine ⟨fun j => ⟨⟨j.val, by omega⟩, j.isLt⟩, 
         fun x => ⟨x.val.val, x.prop⟩, ?_, ?_⟩
  · intro j; rfl
  · intro x; rfl

/-- Equivalence between Fin (n-k) and the subtype {i : Fin n // ¬(i.val < k)}. -/
noncomputable def finEquivSubtypeGe (n k : ℕ) (hk : k ≤ n) : 
    Fin (n - k) ≃ {i : Fin n // ¬ltPred n k i} := by
  refine ⟨fun j => ⟨⟨j.val + k, ?_⟩, ?_⟩, 
         fun x => ⟨x.val.val - k, ?_⟩, ?_, ?_⟩
  · have hj := j.isLt; omega
  · have hj := j.isLt; simp only [ltPred, not_lt]; omega
  · have hx := x.prop
    have hxlt := x.val.isLt
    simp only [ltPred] at hx
    push Not at hx
    omega
  · intro j
    simp only [Fin.ext_iff]
    have hj := j.isLt
    have : j.val + k - k = j.val := Nat.add_sub_cancel j.val k
    exact this
  · intro x
    simp only [Subtype.ext_iff, Fin.ext_iff]
    have hx := x.prop
    simp only [ltPred] at hx
    push Not at hx
    have : x.val.val - k + k = x.val.val := Nat.sub_add_cancel hx
    exact this

/-- Convert restrictToLt to a permutation on Fin k using finEquivSubtypeLt. -/
noncomputable def restrictToLtAsFink {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin n)) 
    (hσ : preservesPrefix σ k) : Equiv.Perm (Fin k) :=
  (finEquivSubtypeLt n k hk).symm.permCongr (restrictToLt σ k hσ)

/-- Convert restrictToGe to a permutation on Fin (n-k) using finEquivSubtypeGe. -/
noncomputable def restrictToGeAsFinNK {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin n)) 
    (hσ : preservesPrefix σ k) : Equiv.Perm (Fin (n - k)) :=
  (finEquivSubtypeGe n k hk).symm.permCongr (restrictToGe σ k hσ)
/-!
## Minors of Diagonal Matrices (Lemma lem.det.minors-diag)

For a diagonal matrix D with entries d₁, d₂, ..., dₙ:

(a) det(sub_P^P D) = ∏_{i ∈ P} dᵢ  (principal minors are products of diagonal entries)
(b) If P ≠ Q with |P| = |Q|, then det(sub_P^Q D) = 0  (off-diagonal submatrices have zero det)
-/
/-!
## Determinant of A + D (Theorem thm.det.det(A+D))

When B = D is diagonal with entries d₁, ..., dₙ, the formula for det(A+B) simplifies:
  det(A+D) = ∑_{P ⊆ [n]} det(sub_P^P A) · ∏_{i ∈ [n]\P} dᵢ

The cross terms vanish because det(sub_P̃^Q̃ D) = 0 when P ≠ Q.
-/
/-!
## Determinant of x + D (Proposition prop.det.x+ai)

For the matrix F with entries F_{i,j} = x + d_i [i=j], i.e.,
  F = (x x ... x)
      (x x+d₂ ... x)
      (⋮  ⋮  ⋱  ⋮)
      (x x ... x+dₙ)

we have:
  det F = d₁d₂...dₙ + x ∑_{i=1}^n d₁d₂...d̂ᵢ...dₙ

where d̂ᵢ means "omit dᵢ".

This is useful in graph theory (e.g., Laplacian matrices).
-/


/-- The matrix with x on all entries except diagonal which has x + dᵢ.
    (Used in Proposition prop.det.x+ai) -/
def constPlusDiagMatrix {n : ℕ} (x : R) (d : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => x + if i = j then d i else 0

/-- The set of fixed points of a permutation. -/
def fixedPoints' {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i = i)

/-- The constant x matrix (all entries equal to x). -/
def constMatrix {n : ℕ} (x : R) : Matrix (Fin n) (Fin n) R :=
  fun _ _ => x
/-!
## Characteristic Polynomial Coefficients (Proposition prop.det.charpol-explicit)

The characteristic polynomial of A is det(xI - A) (or det(A + xI) up to sign).
Its coefficients are sums of principal minors:

  det(A + xI) = ∑_{k=0}^n (∑_{P ⊆ [n], |P|=n-k} det(sub_P^P A)) · x^k

The coefficient of x^{n-k} is the sum of all k×k principal minors of A.
-/
/-!
## Pascal Matrix Determinant (Proposition prop.det.pascal-LU)

The Pascal matrix P_n has entries P_{i,j} = C(i+j-2, i-1), i.e.,
  P = (C(0,0) C(1,0) ... C(n-1,0))
      (C(1,1) C(2,1) ... C(n,1))
      (⋮      ⋮      ⋱   ⋮)
      (C(n-1,n-1) C(n,n-1) ... C(2n-2,n-1))

For n=4, this is:
  (1 1 1 1)
  (1 2 3 4)
  (1 3 6 10)
  (1 4 10 20)

The determinant is 1, which can be proven via LU decomposition.
-/

/-- The Pascal matrix with entries C(i+j, i).
    (Proposition prop.det.pascal-LU)

    Note: We use 0-indexing, so entry (i,j) is C(i+j, i). -/
def pascalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => (i.val + j.val).choose i.val

/-- The lower triangular factor L in the LU decomposition of the Pascal matrix.
    L_{i,k} = C(i, k) -/
def pascalLowerTriangular (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i k => i.val.choose k.val

/-- The upper triangular factor U in the LU decomposition of the Pascal matrix.
    U_{k,j} = C(j, k) -/
def pascalUpperTriangular (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun k j => j.val.choose k.val
/-!
## Additional Lemmas

Some auxiliary results used in the main theorems.
-/

end CauchyBinet

end AlgebraicCombinatorics
