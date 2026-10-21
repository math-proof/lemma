import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.CoeffRothLastEquiv_RothMvHasse_RothLastIndex.eq.RothMvHasse_CoeffHasseDerivRothLastEquiv.of.RothMvIndex
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
  {n : ℕ} [CommSemiring R]
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
  rw [rothLastSlice, finsetSum_coeff]
  if ha : a ∈ (rothLastEquiv ℤ n P).support then
    rw [Finset.sum_eq_single a]
    ·
      simp [lastEquiv_coeff_coeff]
    ·
      intro b hb hba
      simp [coeff_monomial, hba]
    ·
      exact fun hnot ↦ (hnot ha).elim
  else
    rw [Finset.sum_eq_zero]
    ·
      rw [← lastEquiv_coeff_coeff]
      simpa using (congrArg (fun Q : MvPolynomial (Fin n) ℤ ↦ Q.coeff i)
        (notMem_support_iff.mp ha)).symm
    ·
      intro b hb
      have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
      simp [coeff_monomial, hba]

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

private lemma mvHasse_eval_zero
  {m : ℕ} [CommSemiring R]
  (P : MvPolynomial (Fin m) R)
  (i : RothMvIndex m) :
    MvPolynomial.eval (0 : Fin m → R) (rothMvHasse i P) = P.coeff i := by
  rw [MvPolynomial.eval_zero]
  change (rothMvHasse i P).coeff 0 = P.coeff i
  rw [mvHasse_coeff]
  simp

private lemma lastEquiv_eval
  {n : ℕ} [CommSemiring R]
  (x : Fin n → R)
  (y : R)
  (P : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval (Fin.lastCases y x) P =
      eval y (map (MvPolynomial.eval x) (rothLastEquiv R n P)) := by
  have h := MvPolynomial.optionEquivLeft_elim_eval R (Fin n) x y
    ((MvPolynomial.renameEquiv R finSuccEquivLast) P)
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename] at h
  change MvPolynomial.eval _ P = _ at h
  have hfun : (fun z : Fin (n + 1) ↦ Fin.lastCases y x z) =
      (fun z : Option (Fin n) ↦ z.elim y x) ∘ finSuccEquivLast := by
    funext z
    refine Fin.lastCases ?_ (fun j ↦ ?_) z <;> simp
  rw [hfun]
  simpa [rothLastEquiv] using h

/--
[rothLastSlice_hasse_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  (P : MvPolynomial (Fin (n + 1)) ℤ)
  (i : RothMvIndex n)
  (a : ℕ)
  (y : ℚ) :
-- imply
  MvPolynomial.eval (Fin.lastCases y (fun _ ↦ (0 : ℚ)))
      (rothMvHasse (rothLastIndex i a)
        (MvPolynomial.map (algebraMap ℤ ℚ) P)) =
    (hasseDeriv a (map (algebraMap ℤ ℚ) (rothLastSlice P i))).eval y := by
-- proof
  rw [lastEquiv_eval]
  congr 1
  apply ext
  intro b
  rw [coeff_map, CoeffRothLastEquiv_RothMvHasse_RothLastIndex.eq.RothMvHasse_CoeffHasseDerivRothLastEquiv.of.RothMvIndex]
  change MvPolynomial.eval (0 : Fin n → ℚ) _ = _
  rw [mvHasse_eval_zero]
  simp only [hasseDeriv_coeff, coeff_map]
  rw [lastSlice_coeff]
  rw [← MvPolynomial.C_eq_coe_nat, ← MvPolynomial.smul_eq_C_mul,
    MvPolynomial.coeff_smul]
  rw [lastEquiv_coeff_coeff, MvPolynomial.coeff_map]
  simp [smul_eq_mul]


-- created on 2026-10-21
