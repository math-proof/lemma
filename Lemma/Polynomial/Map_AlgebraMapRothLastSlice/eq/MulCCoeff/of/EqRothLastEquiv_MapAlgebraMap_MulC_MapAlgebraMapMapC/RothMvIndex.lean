import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


private lemma equivMapDomain_symm
  {A B M : Type*} [Zero M]
  (e : A ≃ B)
  (d : Finsupp B M) :
    Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm d) = d := by
  ext b
  simp [Finsupp.equivMapDomain_apply]

private lemma lastEquiv_coeff_coeff
  {n : ℕ} {R : Type*} [CommSemiring R]
  (P : MvPolynomial (Fin (n + 1)) R)
  (a : ℕ)
  (i : RothMvIndex n) :
    ((rothLastEquiv R n P).coeff a).coeff i = P.coeff (rothLastIndex i a) := by
  let d := rothLastIndex i a
  have hmap : Finsupp.mapDomain finSuccEquivLast d = Finsupp.optionElim a i := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain]
    change (Finsupp.equivCongrLeft finSuccEquivLast) d = _
    simpa [d, rothLastIndex, Finsupp.equivCongrLeft_apply] using
      equivMapDomain_symm finSuccEquivLast (Finsupp.optionElim a i)
  unfold rothLastEquiv
  rw [AlgEquiv.trans_apply, MvPolynomial.optionEquivLeft_coeff_coeff]
  rw [← hmap, MvPolynomial.renameEquiv_apply,
    MvPolynomial.coeff_rename_mapDomain finSuccEquivLast finSuccEquivLast.injective]

private lemma lastSlice_coeff
  {n : ℕ}
  (P : MvPolynomial (Fin (n + 1)) ℤ)
  (i : RothMvIndex n)
  (a : ℕ) :
    (rothLastSlice P i).coeff a = P.coeff (rothLastIndex i a) := by
  classical
  rw [rothLastSlice, Polynomial.finsetSum_coeff]
  if ha : a ∈ (rothLastEquiv ℤ n P).support then
    rw [Finset.sum_eq_single a]
    ·
      simp [lastEquiv_coeff_coeff]
    ·
      intro b hb hba
      simp [Polynomial.coeff_monomial, hba]
    ·
      exact fun hnot ↦ (hnot ha).elim
  else
    rw [Finset.sum_eq_zero]
    ·
      rw [← lastEquiv_coeff_coeff]
      simpa using (congrArg (fun Q : MvPolynomial (Fin n) ℤ ↦ Q.coeff i)
        (Polynomial.notMem_support_iff.mp ha)).symm
    ·
      intro b hb
      have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
      simp [Polynomial.coeff_monomial, hba]

/--
[rothLastSlice_map_eq_C_mul_of_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  (U : MvPolynomial (Fin (n + 1)) ℤ)
  (V : MvPolynomial (Fin n) ℤ)
  (W : ℚ[X])
  (i : RothMvIndex n)
-- given
  (hfactor :
    rothLastEquiv ℚ n (MvPolynomial.map (algebraMap ℤ ℚ) U) =
      C (MvPolynomial.map (algebraMap ℤ ℚ) V) *
        map MvPolynomial.C W) :
-- imply
  map (algebraMap ℤ ℚ) (rothLastSlice U i) =
    C (V.coeff i : ℚ) * W := by
-- proof
  ext a
  have hcoeff := congrArg
    (fun Q : Polynomial (MvPolynomial (Fin n) ℚ) ↦ (Q.coeff a).coeff i) hfactor
  rw [coeff_map, lastSlice_coeff]
  rw [lastEquiv_coeff_coeff, MvPolynomial.coeff_map] at hcoeff
  simp only [coeff_C_mul, coeff_map] at hcoeff
  rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hcoeff
  simpa [mul_comm] using hcoeff


-- created on 2026-10-21
