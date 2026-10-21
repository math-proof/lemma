import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
import Lemma.Fin.EqRothMvHasse0
import Lemma.Fin.RothMvHasse0.eq.Zero.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothTranslate_coeff_eq_eval_hasse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {m : ℕ}
  (x : Fin m → R) (P : MvPolynomial (Fin m) R) (i : RothMvIndex m) :
-- imply
  (rothTranslate m x P).coeff i = MvPolynomial.eval x (rothMvHasse i P) := by
-- proof
  have rothTranslate_C :
    ∀ {m : ℕ} (x : Fin m → R) (c : R),
      rothTranslate m x (MvPolynomial.C c) = MvPolynomial.C c := by
    intro m
    induction m with
    | zero =>
      intro x c
      simp [rothTranslate]
    | succ n ih =>
      intro x c
      have hC : MvPolynomial.finSuccEquiv R n (MvPolynomial.C c) =
          Polynomial.C (MvPolynomial.C c) := by
        change (MvPolynomial.finSuccEquiv R n) (algebraMap R _ c) =
          Polynomial.C (algebraMap R _ c)
        apply (MvPolynomial.finSuccEquiv R n).commutes c
      apply (MvPolynomial.finSuccEquiv R n).injective
      simp [rothTranslate, hC, ih]
  have rothTranslate_coeff_cons {n : ℕ}
    (x : Fin (n + 1) → R) (P : MvPolynomial (Fin (n + 1)) R)
    (a : ℕ) (i : RothMvIndex n) :
    (rothTranslate (n + 1) x P).coeff (i.cons a) =
      (rothTranslate n (fun h ↦ x h.succ)
        ((Polynomial.taylor (MvPolynomial.C (x 0))
          (MvPolynomial.finSuccEquiv R n P)).coeff a)).coeff i := by
    rw [← MvPolynomial.finSuccEquiv_coeff_coeff i (rothTranslate (n + 1) x P) a]
    simp only [rothTranslate, AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk,
      AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.toRingHom_eq_coe,
      AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, RingEquiv.coe_mk, EquivLike.coe_coe, Polynomial.coe_mapRingHom,
      Function.comp_apply, Polynomial.taylorAlgHom_apply, Polynomial.map_taylor,
      AlgEquiv.apply_symm_apply]
    rw [← Polynomial.map_taylor, Polynomial.coeff_map]
  have rothMvHasse_finSucc_coeff {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R) (a k : ℕ) (i : RothMvIndex n) :
    ((MvPolynomial.finSuccEquiv R n) (rothMvHasse (i.cons a) P)).coeff k =
      rothMvHasse i
        ((Polynomial.hasseDeriv a ((MvPolynomial.finSuccEquiv R n) P)).coeff k) := by
    ext l
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    rw [show (i.cons a : RothMvIndex (n + 1)) = Finsupp.cons a i from rfl]
    rw [show (l.cons k : RothMvIndex (n + 1)) = Finsupp.cons k l from rfl]
    rw [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
      CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
      Polynomial.hasseDeriv_coeff]
    simp only [Fin.prod_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ,
      Finsupp.add_apply]
    rw [show (↑((k + a).choose a) : MvPolynomial (Fin n) R) =
      MvPolynomial.C ((k + a).choose a : R) by simp]
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.finSuccEquiv_coeff_coeff]
    have hcons : Finsupp.cons k l + Finsupp.cons a i =
        Finsupp.cons (k + a) (l + i) := by
      ext h
      refine Fin.cases ?_ (fun h ↦ ?_) h <;> simp
    rw [hcons]
    ac_rfl
  have rothTranslate_eval_coeff {m : ℕ}
    (x : Fin m → R) (p : Polynomial (MvPolynomial (Fin m) R)) (y : R)
    (i : RothMvIndex m) :
    (rothTranslate m x (Polynomial.eval (MvPolynomial.C y) p)).coeff i =
      ∑ k ∈ p.support, (rothTranslate m x (p.coeff k)).coeff i * y ^ k := by
    rw [Polynomial.eval_eq_sum]
    rw [Polynomial.sum_def, map_sum, MvPolynomial.coeff_sum]
    congr with k
    rw [map_mul, map_pow, rothTranslate_C]
    rw [← MvPolynomial.C_pow, mul_comm, MvPolynomial.coeff_C_mul]
    ac_rfl
  revert x P i
  induction m with
  | zero =>
    intro x P i
    have hx : x = 0 := Subsingleton.elim _ _
    have hi : i = 0 := Subsingleton.elim _ _
    subst x
    subst i
    rw [EqRothMvHasse0]
    change P.coeff 0 = MvPolynomial.eval (0 : Fin 0 → R) P
    rw [MvPolynomial.eval_zero]
    rfl
  | succ n ih =>
    intro x P i
    let a : ℕ := i 0
    let it : RothMvIndex n := i.tail
    let xt : Fin n → R := fun h ↦ x h.succ
    let p : Polynomial (MvPolynomial (Fin n) R) := MvPolynomial.finSuccEquiv R n P
    let A : Polynomial (MvPolynomial (Fin n) R) := Polynomial.hasseDeriv a p
    let B : Polynomial (MvPolynomial (Fin n) R) :=
      MvPolynomial.finSuccEquiv R n (rothMvHasse (it.cons a) P)
    have hi : it.cons a = i := by
      simp [a, it]
    rw [← hi, rothTranslate_coeff_cons]
    change
      (rothTranslate n xt
        ((Polynomial.taylor (MvPolynomial.C (x 0)) p).coeff a)).coeff it = _
    rw [Polynomial.taylor_coeff]
    change (rothTranslate n xt (Polynomial.eval (MvPolynomial.C (x 0)) A)).coeff it = _
    rw [rothTranslate_eval_coeff]
    have hx : x = Fin.cons (x 0) xt := by
      ext h
      refine Fin.cases ?_ (fun h ↦ ?_) h <;> simp [xt]
    rw [hx, MvPolynomial.eval_eq_eval_mv_eval']
    change (∑ k ∈ A.support, (rothTranslate n xt (A.coeff k)).coeff it * x 0 ^ k) =
      Polynomial.eval (x 0) (Polynomial.map (MvPolynomial.eval xt) B)
    have hBA : B.support ⊆ A.support := by
      intro k hk
      by_contra hkA
      have hAk : A.coeff k = 0 := Polynomial.notMem_support_iff.mp hkA
      have hBk := rothMvHasse_finSucc_coeff P a k it
      change B.coeff k = rothMvHasse it (A.coeff k) at hBk
      rw [hAk, RothMvHasse0.eq.Zero.of.RothMvIndex] at hBk
      apply (Polynomial.mem_support_iff.mp hk) hBk
    have hmap : (Polynomial.map (MvPolynomial.eval xt) B).support ⊆ A.support :=
      (Polynomial.support_map_subset (MvPolynomial.eval xt) B).trans hBA
    rw [Polynomial.eval_eq_sum]
    rw [Polynomial.sum_eq_of_subset (fun e c ↦ c * x 0 ^ e) (by simp) hmap]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Polynomial.coeff_map]
    have hBk := rothMvHasse_finSucc_coeff P a k it
    change B.coeff k = rothMvHasse it (A.coeff k) at hBk
    rw [hBk, ← ih xt (A.coeff k) it]


-- created on 2026-10-21
