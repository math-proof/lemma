import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.CoeffRothLastEquiv_RothMvHasse_RothLastIndex.eq.RothMvHasse_CoeffHasseDerivRothLastEquiv.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


private lemma mvHasse_coeff
  {m : ℕ} [CommSemiring R]
  (i k : RothMvIndex m)
  (P : MvPolynomial (Fin m) R) :
    (rothMvHasse i P).coeff k =
      (∏ h, (Nat.choose ((k + i) h) (i h) : R)) * P.coeff (k + i) := by
  classical
  unfold rothMvHasse
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single (k + i)]
  ·
    have hki : k + i - i = k := by
      ext h
      simp
    simp only [hki, ite_true]
  ·
    intro j hj hne
    split_ifs with heq
    ·
      if hle : i ≤ j then
        exfalso
        apply hne
        ext h
        have heqh := congrArg (fun x : RothMvIndex m ↦ x h) heq
        have hleh := hle h
        simp only [Finsupp.add_apply]
        exact (tsub_eq_iff_eq_add_of_le hleh).mp heqh
      else
        obtain ⟨h, hh⟩ := not_forall.mp hle
        push Not at hh
        have hz : (Nat.choose (j h) (i h) : R) = 0 := by
          simp [Nat.choose_eq_zero_of_lt hh]
        rw [Finset.prod_eq_zero (Finset.mem_univ h) hz, zero_mul]
    ·
      simp
  ·
    intro hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp

private lemma mvHasse_zero
  {m : ℕ} [CommSemiring R]
  (i : RothMvIndex m) :
    rothMvHasse i (0 : MvPolynomial (Fin m) R) = 0 := by
  simp [rothMvHasse]

private lemma mvHasse_add
  {m : ℕ} [CommSemiring R]
  (i : RothMvIndex m)
  (P Q : MvPolynomial (Fin m) R) :
    rothMvHasse i (P + Q) = rothMvHasse i P + rothMvHasse i Q := by
  ext k
  simp only [mvHasse_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]

private lemma mvHasse_smul
  {m : ℕ} [CommSemiring R]
  (i : RothMvIndex m)
  (c : R)
  (P : MvPolynomial (Fin m) R) :
    rothMvHasse i (c • P) = c • rothMvHasse i P := by
  ext k
  simp only [mvHasse_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  ring

private lemma mvHasse_finset_sum
  {m : ℕ} [CommSemiring R]
  {ι : Type*}
  (s : Finset ι)
  (i : RothMvIndex m)
  (P : ι → MvPolynomial (Fin m) R) :
    rothMvHasse i (∑ a ∈ s, P a) = ∑ a ∈ s, rothMvHasse i (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [mvHasse_zero]
  | @insert a s ha ih =>
    simp [ha, mvHasse_add, ih]

/--
[rothLastEquiv_hasse_of_tensor_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n k : ℕ}
  (Q : Polynomial (MvPolynomial (Fin n) ℚ))
  (phi : Fin k → MvPolynomial (Fin n) ℚ)
  (psi : Fin k → ℚ[X])
-- given
  (hQ : Q = ∑ j, C (phi j) * map MvPolynomial.C (psi j))
  (i : RothMvIndex n)
  (a : ℕ) :
-- imply
  rothLastEquiv ℚ n
    (rothMvHasse (rothLastIndex i a) ((rothLastEquiv ℚ n).symm Q)) =
    ∑ j, C (rothMvHasse i (phi j)) *
      map MvPolynomial.C (hasseDeriv a (psi j)) := by
-- proof
  ext b l
  rw [CoeffRothLastEquiv_RothMvHasse_RothLastIndex.eq.RothMvHasse_CoeffHasseDerivRothLastEquiv.of.RothMvIndex,
    AlgEquiv.apply_symm_apply, finsetSum_coeff]
  simp only [coeff_C_mul, hasseDeriv_coeff]
  rw [hQ, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_map]
  rw [← MvPolynomial.C_eq_coe_nat, ← MvPolynomial.smul_eq_C_mul,
    mvHasse_smul, mvHasse_finset_sum, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_sum]
  rw [Finset.smul_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hphi : phi j * MvPolynomial.C ((psi j).coeff (b + a)) =
    (psi j).coeff (b + a) • phi j := by
    rw [MvPolynomial.smul_eq_C_mul]
    ring
  rw [hphi, mvHasse_smul, MvPolynomial.coeff_smul]
  simp only [smul_eq_mul]
  rw [mul_comm (rothMvHasse i (phi j)), MvPolynomial.coeff_C_mul,
    hasseDeriv_coeff]
  ring


-- created on 2026-10-21
