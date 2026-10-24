import Mathlib
import sympy.Basic
import sympy.combinatorics.symmetric.SSYTEquiv
import Lemma.MvPolynomial.SchurBasics
import Lemma.MvPolynomial.PieriJacobiTrudi
open SSYTEquiv
open Finset
open MvPolynomial hiding R
open scoped BigOperators Classical


section
-- ac-theorems

open Finset BigOperators MvPolynomial

namespace SSYTEquiv

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
@[simp]
lemma npartitionEquiv_apply (lam : NPartition N) :
    npartitionEquiv lam = schurBasicsNPartition_to_SF lam := rfl

omit [NeZero N] in
@[simp]
lemma npartitionEquiv_symm_apply (lam : SymmetricFunctions.NPartition N) :
    npartitionEquiv.symm lam = sfNPartition_to_SchurBasics lam := rfl

omit [NeZero N] in
/-- The equivalence `npartitionEquiv` is the symmetric of `NPartition.equivShared`
    from PieriJacobiTrudi.lean. This means code can use either:
    - `npartitionEquiv lam` to go from shared → local
    - `lam.toShared` to go from local → shared -/
lemma npartitionEquiv_eq_equivShared_symm :
    (npartitionEquiv (N := N)) = SymmetricFunctions.NPartition.equivShared.symm := by
  ext lam
  rfl

omit [NeZero N] in
/-- The outer partition contains the inner partition after conversion. -/
lemma sfSkewPartition_contained (s : SymmetricFunctions.SkewPartition N) :
    (sfSkewPartition_to_SchurBasics s).2 ≤ (sfSkewPartition_to_SchurBasics s).1 := by
  intro i
  simp only [sfSkewPartition_to_SchurBasics, sfNPartition_to_SchurBasics_parts]
  exact s.contained i


/-- The monomial associated to a SymmetricFunctions.SSYT equals the monomial of the
    corresponding SchurBasics.SSYT (as a product over cells).

    This is the key lemma for proving Schur polynomial equivalence.
    The proof shows that the product over cells is preserved by the bijection. -/
lemma toSchurBasicsSSYT_monomial_eq {R : Type*} [CommRing R]
    {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    (T.toMonomial : MvPolynomial (Fin N) R) =
    ∏ c : { c // c ∈ (sfNPartition_to_SchurBasics lam).youngDiagram },
      X ((toSchurBasicsSSYT T).entry c.val) := by
  -- T.toMonomial = ∏ i, ∏ j : Fin (lam.parts i), X (T.entries i j)
  -- RHS = ∏ c ∈ youngDiagram, X ((toSchurBasicsSSYT T).entry c)
  -- Both are products over the same cells, with the same values
  -- The proof requires showing the bijection between (i, j : Fin (lam.parts i))
  -- and cells c ∈ youngDiagram preserves the monomial factors
  unfold SymmetricFunctions.SSYT.toMonomial
  -- First, show that the entry values match under the bijection
  have h_entry : ∀ (i : Fin N) (j : Fin (lam.parts i)),
      (X (T.entries i j) : MvPolynomial (Fin N) R) =
      X ((toSchurBasicsSSYT T).entry (i, j.val)) := by
    intro i j
    simp only [toSchurBasicsSSYT]
    have hj_lt : j.val < lam.parts i := j.isLt
    simp only [hj_lt, ↓reduceDIte]
  -- Rewrite the LHS using Fintype.prod_sigma'
  rw [← Fintype.prod_sigma']
  -- Define the equivalence
  let e : (Σ i : Fin N, Fin (lam.parts i)) ≃
      { c // c ∈ (sfNPartition_to_SchurBasics lam).youngDiagram } := {
    toFun := fun ⟨i, j⟩ => ⟨(i, j.val), by
      rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact j.isLt⟩
    invFun := fun ⟨c, hc⟩ => ⟨c.1, ⟨c.2, by
      rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc
      exact hc⟩⟩
    left_inv := fun ⟨i, j⟩ => rfl
    right_inv := fun ⟨c, hc⟩ => rfl
  }
  -- Now use the equivalence
  rw [Fintype.prod_equiv e]
  intro ⟨i, j⟩
  simp only [e, Equiv.coe_fn_mk]
  rw [h_entry i j]

/-- The conversion from SF SSYT to Filling satisfies the SSYT condition. -/
lemma sfSSYT_to_Filling_isSSYT {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    isSSYTFillingYoung (sfNPartition_to_SchurBasics lam) (sfSSYT_to_Filling T) := by
  constructor
  · -- Row-weak condition: same row (c1.1 = c2.1), c1.2 < c2.2
    intro c1 c2 hrow hcol
    simp only [sfSSYT_to_Filling]
    have hc1_mem := c1.prop
    have hc2_mem := c2.prop
    simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc1_mem hc2_mem
    -- hrow says c1.val.1 = c2.val.1 (same row)
    -- hcol says c1.val.2 < c2.val.2 (c1 is to the left of c2)
    have hc1_lt : c1.val.2 < lam.parts c1.val.1 := hc1_mem
    have hc2_lt : c2.val.2 < lam.parts c2.val.1 := hc2_mem
    -- Since c1.1 = c2.1, we can rewrite
    have hc1_lt' : c1.val.2 < lam.parts c2.val.1 := by rw [← hrow]; exact hc1_lt
    -- Apply rowWeak: entries at (c2.1, c1.2) ≤ entries at (c2.1, c2.2)
    have h := T.rowWeak c2.val.1 ⟨c1.val.2, hc1_lt'⟩ ⟨c2.val.2, hc2_lt⟩ (Nat.le_of_lt hcol)
    -- Need to show: T.entries c1.1 ⟨c1.2, _⟩ ≤ T.entries c2.1 ⟨c2.2, _⟩
    -- Since c1.1 = c2.1, rewrite using hrow
    cases c1 with | mk c1val c1prop =>
    cases c2 with | mk c2val c2prop =>
    simp only [Subtype.coe_mk] at hrow hcol hc1_lt hc2_lt hc1_lt' h ⊢
    cases c1val with | mk c1fst c1snd =>
    cases c2val with | mk c2fst c2snd =>
    simp only at hrow
    simp only at hrow hcol hc1_lt hc2_lt hc1_lt' h ⊢
    subst hrow
    exact h
  · -- Column-strict condition: same column (c1.2 = c2.2), c1.1 < c2.1
    intro c1 c2 hcol hrow
    simp only [sfSSYT_to_Filling]
    have hc1_mem := c1.prop
    have hc2_mem := c2.prop
    simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc1_mem hc2_mem
    -- hcol says c1.val.2 = c2.val.2 (same column)
    -- hrow says c1.val.1 < c2.val.1 (c1 is above c2)
    have hc1_lt : c1.val.2 < lam.parts c1.val.1 := hc1_mem
    have hc2_lt : c2.val.2 < lam.parts c2.val.1 := hc2_mem
    -- Since c1.2 = c2.2 and c2.2 < lam.parts c2.1, we have c1.2 < lam.parts c2.1
    have hc1_lt' : c1.val.2 < lam.parts c2.val.1 := by rw [hcol]; exact hc2_lt
    -- Apply sf_ssyt_col_strict_nonadjacent
    have h := sf_ssyt_col_strict_nonadjacent T hc1_lt hc1_lt' hrow
    -- Need to show: T.entries c1.1 ⟨c1.2, _⟩ < T.entries c2.1 ⟨c2.2, _⟩
    convert h using 3
    · exact hcol.symm

/-- The conversions are inverses (SF SSYT → Filling → SF SSYT). -/
lemma filling_sfSSYT_id {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    filling_to_sfSSYT (sfSSYT_to_Filling T) (sfSSYT_to_Filling_isSSYT T) = T := by
  apply SSYT_eq_of_entries_eq
  funext i j
  simp only [filling_to_sfSSYT, sfSSYT_to_Filling]

/-- The conversions are inverses (Filling → SF SSYT → Filling). -/
lemma sfSSYT_filling_id {lam : SymmetricFunctions.NPartition N}
    (f : Filling (sfNPartition_to_SchurBasics lam))
    (hf : isSSYTFillingYoung (sfNPartition_to_SchurBasics lam) f) :
    sfSSYT_to_Filling (filling_to_sfSSYT f hf) = f := by
  funext c
  simp only [sfSSYT_to_Filling, filling_to_sfSSYT]

/-- The monomial of an SF SSYT equals the monomial of the corresponding Filling. -/
lemma sfSSYT_monomial_eq_filling {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    (T.toMonomial : MvPolynomial (Fin N) ℤ) =
    fillingMonomialYoung (sfSSYT_to_Filling T) := by
  unfold SymmetricFunctions.SSYT.toMonomial fillingMonomialYoung sfSSYT_to_Filling
  -- Both are products over the cells of the Young diagram
  -- LHS: ∏ i, ∏ j : Fin (lam.parts i), X (T.entries i j)
  -- RHS: ∏ c : { c // c ∈ youngDiagram }, X (T.entries c.1 ⟨c.2, _⟩)
  rw [← Fintype.prod_sigma']
  -- Define the equivalence between (Σ i, Fin (lam.parts i)) and { c // c ∈ youngDiagram }
  let e : (Σ i : Fin N, Fin (lam.parts i)) ≃
      { c // c ∈ (sfNPartition_to_SchurBasics lam).youngDiagram } := {
    toFun := fun ⟨i, j⟩ => ⟨(i, j.val), by
      rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact j.isLt⟩
    invFun := fun ⟨c, hc⟩ => ⟨c.1, ⟨c.2, by
      rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc
      exact hc⟩⟩
    left_inv := fun ⟨i, j⟩ => rfl
    right_inv := fun ⟨c, hc⟩ => rfl
  }
  rw [Fintype.prod_equiv e]
  intro ⟨i, j⟩
  rfl

/-- The Schur polynomial from PieriJacobiTrudi equals the Schur polynomial from SchurBasics
    when specialized to coefficient ring ℤ.

    This theorem establishes that `SymmetricFunctions.schur lam` (over ℤ) equals
    `schurPoly (sfNPartition_to_SchurBasics lam)`.

    **Note**: This theorem requires `[NeZero N]` because `schurPoly` requires it.
    For the generic ring version, see `schur_eq_schurPoly_map`. -/
lemma schur_eq_schurPoly_int (lam : SymmetricFunctions.NPartition N) :
    (SymmetricFunctions.schur (R := ℤ) lam : MvPolynomial (Fin N) ℤ) =
    schurPoly (sfNPartition_to_SchurBasics lam) := by
  -- Both are sums over SSYT, we need to show the sums are equal
  -- schur lam = ∑ T ∈ ssytFinset lam, T.toMonomial
  -- schurPoly lam' = ∑ f ∈ ssytFillingsYoung lam', fillingMonomialYoung f
  unfold SymmetricFunctions.schur schurPoly ssytFillingsYoung
  -- Use Finset.sum_bij to establish the bijection
  apply Finset.sum_bij (fun T _ => sfSSYT_to_Filling T)
  · -- hi: sfSSYT_to_Filling maps ssytFinset to ssytFillingsYoung
    intro T _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact sfSSYT_to_Filling_isSSYT T
  · -- i_inj: sfSSYT_to_Filling is injective
    intro T1 _ T2 _ heq
    apply SSYT_eq_of_entries_eq
    funext i j
    have h1 := congrFun heq ⟨(i, j.val), by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact j.isLt⟩
    simp only [sfSSYT_to_Filling] at h1
    exact h1
  · -- i_surj: sfSSYT_to_Filling is surjective onto ssytFillingsYoung
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    refine ⟨filling_to_sfSSYT f hf, SymmetricFunctions.ssytFinset_mem lam _, ?_⟩
    exact sfSSYT_filling_id f hf
  · -- h: monomials are preserved
    intro T _
    exact sfSSYT_monomial_eq_filling T

/-- Corollary: The two Schur polynomial definitions are equal up to NPartition conversion.

    This is the main user-facing theorem for composing results from different files. -/
lemma schurPoly_eq_schur (lam : NPartition N) :
    (schurPoly lam : MvPolynomial (Fin N) ℤ) =
    SymmetricFunctions.schur (schurBasicsNPartition_to_SF lam) := by
  rw [schur_eq_schurPoly_int]
  simp only [sfNPartition_schurBasics_id]

end SSYTEquiv

end


/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_sfNPartition_schurBasics_id
  {N : ℕ} [NeZero N]
-- given
  (lam : NPartition N) :
-- imply
  sfNPartition_to_SchurBasics (schurBasicsNPartition_to_SF lam) = lam := by
-- proof
  apply SSYTEquiv.sfNPartition_schurBasics_id lam

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_schurBasics_sfNPartition_id
  {N : ℕ} [NeZero N]
-- given
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  schurBasicsNPartition_to_SF (sfNPartition_to_SchurBasics lam) = lam := by
-- proof
  apply SSYTEquiv.schurBasics_sfNPartition_id lam

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_schurBasicsNPartition_to_SF_parts
  {N : ℕ} [NeZero N]
-- given
  (lam : NPartition N) :
-- imply
  (schurBasicsNPartition_to_SF lam).parts = lam.parts := by
-- proof
  apply SSYTEquiv.schurBasicsNPartition_to_SF_parts lam

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_sfNPartition_to_SchurBasics_parts
  {N : ℕ} [NeZero N]
-- given
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  (sfNPartition_to_SchurBasics lam).parts = lam.parts := by
-- proof
  apply SSYTEquiv.sfNPartition_to_SchurBasics_parts lam

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_npartitionEquiv_apply
  {N : ℕ} [NeZero N]
-- given
  (lam : NPartition N) :
-- imply
  npartitionEquiv lam = schurBasicsNPartition_to_SF lam := by
-- proof
  apply SSYTEquiv.npartitionEquiv_apply lam

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_npartitionEquiv_symm_apply
  {N : ℕ} [NeZero N]
-- given
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  npartitionEquiv.symm lam = sfNPartition_to_SchurBasics lam := by
-- proof
  apply SSYTEquiv.npartitionEquiv_symm_apply lam

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_npartitionEquiv_eq_equivShared_symm
  {N : ℕ} [NeZero N] :
-- imply
  (npartitionEquiv (N := N)) = SymmetricFunctions.NPartition.equivShared.symm := by
-- proof
  apply SSYTEquiv.npartitionEquiv_eq_equivShared_symm

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_sf_ssyt_col_strict_nonadjacent
  {N : ℕ} [NeZero N]
  {lam : SymmetricFunctions.NPartition N}
  {i₁ i₂ : Fin N}
  {j : ℕ}
-- given
  (hj₁ : j < lam.parts i₁)
  (hj₂ : j < lam.parts i₂)
  (hi : i₁ < i₂)
  (T : SymmetricFunctions.SSYT lam) :
-- imply
  T.entries i₁ ⟨j, hj₁⟩ < T.entries i₂ ⟨j, hj₂⟩ := by
-- proof
  apply SSYTEquiv.sf_ssyt_col_strict_nonadjacent T hj₁ hj₂ hi

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_SSYT_eq_of_entries_eq
  {N : ℕ} [NeZero N]
  {lam : SymmetricFunctions.NPartition N}
  {T1 T2 : SymmetricFunctions.SSYT lam}
-- given
  (h : T1.entries = T2.entries) :
-- imply
  T1 = T2 := by
-- proof
  apply SSYTEquiv.SSYT_eq_of_entries_eq h

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_toSFSSYT_toSchurBasicsSSYT
  {N : ℕ} [NeZero N]
  {lam : SymmetricFunctions.NPartition N}
-- given
  (T : SymmetricFunctions.SSYT lam) :
-- imply
  toSFSSYT (toSchurBasicsSSYT T) = T := by
-- proof
  apply SSYTEquiv.toSFSSYT_toSchurBasicsSSYT T

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_toSchurBasicsSSYT_toSFSSYT
  {N : ℕ} [NeZero N]
  {lam : NPartition N}
-- given
  (T : SSYT lam) :
-- imply
  toSchurBasicsSSYT (toSFSSYT T) = T := by
-- proof
  apply SSYTEquiv.toSchurBasicsSSYT_toSFSSYT T

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_sfSkewPartition_contained
  {N : ℕ} [NeZero N]
-- given
  (s : SymmetricFunctions.SkewPartition N) :
-- imply
  (sfSkewPartition_to_SchurBasics s).2 ≤ (sfSkewPartition_to_SchurBasics s).1 := by
-- proof
  apply SSYTEquiv.sfSkewPartition_contained s

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_toSchurBasicsSSYT_monomial_eq
  [CommRing R]
  {N : ℕ} [NeZero N]
  {lam : SymmetricFunctions.NPartition N}
-- given
  (T : SymmetricFunctions.SSYT lam) :
-- imply
  (T.toMonomial : MvPolynomial (Fin N) R) = ∏ c : Subtype (fun c => c ∈ (sfNPartition_to_SchurBasics lam).youngDiagram), X ((toSchurBasicsSSYT T).entry c.val) := by
-- proof
  apply SSYTEquiv.toSchurBasicsSSYT_monomial_eq T

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_sfSSYT_to_Filling_isSSYT
  {N : ℕ} [NeZero N]
  {lam : SymmetricFunctions.NPartition N}
-- given
  (T : SymmetricFunctions.SSYT lam) :
-- imply
  isSSYTFillingYoung (sfNPartition_to_SchurBasics lam) (sfSSYT_to_Filling T) := by
-- proof
  apply SSYTEquiv.sfSSYT_to_Filling_isSSYT T

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_filling_sfSSYT_id
  {N : ℕ} [NeZero N]
  {lam : SymmetricFunctions.NPartition N}
-- given
  (T : SymmetricFunctions.SSYT lam) :
-- imply
  filling_to_sfSSYT (sfSSYT_to_Filling T) (sfSSYT_to_Filling_isSSYT T) = T := by
-- proof
  apply SSYTEquiv.filling_sfSSYT_id T

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_sfSSYT_filling_id
  {N : ℕ} [NeZero N]
  {lam : SymmetricFunctions.NPartition N}
-- given
  (f : Filling (sfNPartition_to_SchurBasics lam))
  (hf : isSSYTFillingYoung (sfNPartition_to_SchurBasics lam) f) :
-- imply
  sfSSYT_to_Filling (filling_to_sfSSYT f hf) = f := by
-- proof
  apply SSYTEquiv.sfSSYT_filling_id f hf

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_sfSSYT_monomial_eq_filling
  {N : ℕ} [NeZero N]
  {lam : SymmetricFunctions.NPartition N}
-- given
  (T : SymmetricFunctions.SSYT lam) :
-- imply
  (T.toMonomial : MvPolynomial (Fin N) ℤ) = fillingMonomialYoung (sfSSYT_to_Filling T) := by
-- proof
  apply SSYTEquiv.sfSSYT_monomial_eq_filling T

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_schur_eq_schurPoly_int
  {N : ℕ} [NeZero N]
-- given
  (lam : SymmetricFunctions.NPartition N) :
-- imply
  (SymmetricFunctions.schur (R := ℤ) lam : MvPolynomial (Fin N) ℤ) = schurPoly (sfNPartition_to_SchurBasics lam) := by
-- proof
  apply SSYTEquiv.schur_eq_schurPoly_int lam

/--
[SSYTEquiv](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/SSYTEquiv.lean)
-/
@[path]
private lemma se_schurPoly_eq_schur
  {N : ℕ} [NeZero N]
-- given
  (lam : NPartition N) :
-- imply
  (schurPoly lam : MvPolynomial (Fin N) ℤ) = SymmetricFunctions.schur (schurBasicsNPartition_to_SF lam) := by
-- proof
  apply SSYTEquiv.schurPoly_eq_schur lam


-- created on 2026-10-23
