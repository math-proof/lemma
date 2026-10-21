import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Nat.RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial
open Nat


private lemma equivMapDomain_symm
  {A B M : Type*} [Zero M]
  (e : A ≃ B)
  (d : Finsupp B M) :
    Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm d) = d := by
  ext b
  simp [Finsupp.equivMapDomain_apply]

private lemma lastIndex_castSucc
  {n : ℕ}
  (i : RothMvIndex n)
  (a : ℕ)
  (h : Fin n) :
    rothLastIndex i a h.castSucc = i h := by
  have heq : (Finsupp.equivCongrLeft finSuccEquivLast) (rothLastIndex i a) =
      Finsupp.optionElim a i := by
    simpa [rothLastIndex, Finsupp.equivCongrLeft_apply] using
      equivMapDomain_symm finSuccEquivLast (Finsupp.optionElim a i)
  have := congrArg (fun d : Finsupp (Option (Fin n)) ℕ ↦ d (some h)) heq
  simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using this

private lemma lastIndex_last
  {n : ℕ}
  (i : RothMvIndex n)
  (a : ℕ) :
    rothLastIndex i a (Fin.last n) = a := by
  have heq : (Finsupp.equivCongrLeft finSuccEquivLast) (rothLastIndex i a) =
      Finsupp.optionElim a i := by
    simpa [rothLastIndex, Finsupp.equivCongrLeft_apply] using
      equivMapDomain_symm finSuccEquivLast (Finsupp.optionElim a i)
  have := congrArg (fun d : Finsupp (Option (Fin n)) ℕ ↦ d none) heq
  simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using this

private lemma lastIndex_add
  {n : ℕ}
  (i j : RothMvIndex n)
  (a b : ℕ) :
    rothLastIndex (i + j) (a + b) = rothLastIndex i a + rothLastIndex j b := by
  -- use Nat port of the unfolded statement via definitional eq
  simpa [rothLastIndex] using
    RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex i j a b

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

private lemma mvHasse_coeff
  {m : ℕ} {R : Type*} [CommSemiring R]
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

/--
[rothLastEquiv_hasse_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ} [CommSemiring R]
  (P : MvPolynomial (Fin (n + 1)) R)
  (i : RothMvIndex n)
  (a b : ℕ) :
-- imply
  (rothLastEquiv R n (rothMvHasse (rothLastIndex i a) P)).coeff b =
    rothMvHasse i ((hasseDeriv a (rothLastEquiv R n P)).coeff b) := by
-- proof
  ext j
  rw [lastEquiv_coeff_coeff, mvHasse_coeff, mvHasse_coeff,
    hasseDeriv_coeff, ← MvPolynomial.C_eq_coe_nat,
    MvPolynomial.coeff_C_mul, lastEquiv_coeff_coeff]
  rw [Fin.prod_univ_castSucc]
  simp only [lastIndex_add, lastIndex_castSucc, lastIndex_last,
    Finsupp.add_apply]
  ring


-- created on 2026-10-21
