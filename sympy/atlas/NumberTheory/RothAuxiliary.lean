/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic
set_option maxHeartbeats 999999

/-!
This file contains the auxiliary-polynomial machinery shared by Roth's theorem and Ridout's
S-adic extension. The public theorem abstracts their integrality difference as finite divisibility
data; the ordinary archimedean theorem is the specialization with no divisibility places.
-/

open scoped BigOperators

namespace MathlibExt.NumberTheory.RothAuxiliary

open scoped BigOperators nonZeroDivisors Polynomial

attribute [local instance] Matrix.seminormedAddCommGroup

abbrev RothMultiIndex (m : ℕ) := Fin m → ℕ

abbrev RothBox {m : ℕ} (r : Fin m → ℕ) := ∀ h, Fin (r h + 1)

abbrev RothCoeff {m : ℕ} (r : Fin m → ℕ) := RothBox r → ℤ

abbrev RothMvIndex (m : ℕ) := Fin m →₀ ℕ

noncomputable def rothMvHasse {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) (P : MvPolynomial (Fin m) R) : MvPolynomial (Fin m) R :=
  P.coeff.sum fun j c ↦
    MvPolynomial.monomial (j - i) ((∏ h, (Nat.choose (j h) (i h) : R)) * c)

private theorem rothMvHasse_zero {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) : rothMvHasse i (0 : MvPolynomial (Fin m) R) = 0 := by
  simp [rothMvHasse]

private theorem rothMvHasse_zero_index {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) : rothMvHasse 0 P = P := by
  classical
  unfold rothMvHasse
  calc
    _ = P.coeff.sum (fun j c ↦ MvPolynomial.monomial j c) := by
      apply Finsupp.sum_congr
      intro j _hj
      congr 2
      · ext h
        simp
      · simp
    _ = P := by
      rw [Finsupp.sum]
      simpa [MvPolynomial.support] using MvPolynomial.support_sum_monomial_coeff P

private theorem rothMvHasse_coeff {m : ℕ} {R : Type*} [CommSemiring R]
    (i k : RothMvIndex m) (P : MvPolynomial (Fin m) R) :
    (rothMvHasse i P).coeff k =
      (∏ h, (Nat.choose ((k + i) h) (i h) : R)) * P.coeff (k + i) := by
  classical
  unfold rothMvHasse
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single (k + i)]
  · have hki : k + i - i = k := by
      ext h
      simp
    simp only [hki, ite_true]
  · intro j hj hne
    split_ifs with heq
    · by_cases hle : i ≤ j
      · exfalso
        apply hne
        ext h
        have heqh := congrArg (fun x : RothMvIndex m ↦ x h) heq
        have hleh := hle h
        simp only [Finsupp.add_apply]
        exact (tsub_eq_iff_eq_add_of_le hleh).mp heqh
      · obtain ⟨h, hh⟩ := not_forall.mp hle
        push Not at hh
        have hz : (Nat.choose (j h) (i h) : R) = 0 := by
          simp [Nat.choose_eq_zero_of_lt hh]
        rw [Finset.prod_eq_zero (Finset.mem_univ h) hz, zero_mul]
    · simp
  · intro hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp

private theorem rothMvHasse_eval_zero {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) (i : RothMvIndex m) :
    MvPolynomial.eval (0 : Fin m → R) (rothMvHasse i P) = P.coeff i := by
  rw [MvPolynomial.eval_zero]
  change (rothMvHasse i P).coeff 0 = P.coeff i
  rw [rothMvHasse_coeff]
  simp

private theorem roth_choose_comp (l i j : ℕ) :
    (l + j).choose j * (l + j + i).choose i =
      (i + j).choose i * (l + (i + j)).choose (i + j) := by
  have h := Nat.choose_mul (n := l + j + i) (k := i + j) (s := i)
    (Nat.le_add_right i j)
  have hsub : l + j + i - i = l + j := by omega
  rw [hsub] at h
  have hk : i + j - i = j := by omega
  rw [hk] at h
  have htotal : l + j + i = l + (i + j) := by omega
  rw [htotal] at h
  rw [htotal]
  simpa only [mul_comm] using h.symm

private theorem rothMvHasse_comp {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) (i j : RothMvIndex m) :
    rothMvHasse j (rothMvHasse i P) =
      (∏ h, (Nat.choose ((i + j) h) (i h) : R)) • rothMvHasse (i + j) P := by
  ext l
  rw [rothMvHasse_coeff, rothMvHasse_coeff]
  rw [MvPolynomial.coeff_smul, rothMvHasse_coeff]
  rw [smul_eq_mul]
  have hprod :
      (∏ h, (Nat.choose ((l + j) h) (j h) : R)) *
          (∏ h, (Nat.choose ((l + j + i) h) (i h) : R)) =
        (∏ h, (Nat.choose ((i + j) h) (i h) : R)) *
          (∏ h, (Nat.choose ((l + (i + j)) h) ((i + j) h) : R)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro h _hh
    simp only [Finsupp.add_apply]
    rw [← Nat.cast_mul, ← Nat.cast_mul, roth_choose_comp]
  have hindex : l + j + i = l + (i + j) := by
    ext h
    simp only [Finsupp.add_apply]
    omega
  rw [hindex] at hprod
  rw [hindex, ← mul_assoc, ← mul_assoc, hprod]

private theorem rothMvHasse_add {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) (P Q : MvPolynomial (Fin m) R) :
    rothMvHasse i (P + Q) = rothMvHasse i P + rothMvHasse i Q := by
  ext k
  simp only [rothMvHasse_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    mul_add]

private theorem rothMvHasse_smul {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) (c : R) (P : MvPolynomial (Fin m) R) :
    rothMvHasse i (c • P) = c • rothMvHasse i P := by
  ext k
  simp only [rothMvHasse_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  ring

private theorem rothMvHasse_map {m : ℕ} {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (i : RothMvIndex m)
    (P : MvPolynomial (Fin m) R) :
    MvPolynomial.map f (rothMvHasse i P) =
      rothMvHasse i (MvPolynomial.map f P) := by
  ext k
  rw [MvPolynomial.coeff_map, rothMvHasse_coeff, rothMvHasse_coeff,
    MvPolynomial.coeff_map, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro h _hh
  simp

private theorem rothMvHasse_finset_sum {m : ℕ} {R : Type*} [CommSemiring R]
    {ι : Type*} (s : Finset ι) (i : RothMvIndex m)
    (P : ι → MvPolynomial (Fin m) R) :
    rothMvHasse i (∑ a ∈ s, P a) = ∑ a ∈ s, rothMvHasse i (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothMvHasse_zero]
  | @insert a s ha ih => simp [ha, rothMvHasse_add, ih]

noncomputable def rothTranslate {R : Type*} [CommRing R] :
    (m : ℕ) → (Fin m → R) →
      MvPolynomial (Fin m) R →+* MvPolynomial (Fin m) R
  | 0, _ => RingHom.id _
  | n + 1, x =>
      (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.toRingHom.comp
        ((Polynomial.mapRingHom (rothTranslate n (fun h ↦ x h.succ))).comp
          ((Polynomial.taylorAlgHom (R := MvPolynomial (Fin n) R)
              (MvPolynomial.C (x 0))).toRingHom.comp
            (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom))

private theorem rothTranslate_C {R : Type*} [CommRing R] :
    ∀ {m : ℕ} (x : Fin m → R) (c : R),
      rothTranslate m x (MvPolynomial.C c) = MvPolynomial.C c := by
  intro m
  induction m with
  | zero => simp [rothTranslate]
  | succ n ih =>
      intro x c
      have hC : MvPolynomial.finSuccEquiv R n (MvPolynomial.C c) =
          Polynomial.C (MvPolynomial.C c) := by
        change (MvPolynomial.finSuccEquiv R n) (algebraMap R _ c) =
          Polynomial.C (algebraMap R _ c)
        exact (MvPolynomial.finSuccEquiv R n).commutes c
      apply (MvPolynomial.finSuccEquiv R n).injective
      simp [rothTranslate, hC, ih]

private theorem rothTranslate_coeff_cons {R : Type*} [CommRing R] {n : ℕ}
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

private theorem rothMvHasse_finSucc_coeff {n : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin (n + 1)) R) (a k : ℕ) (i : RothMvIndex n) :
    ((MvPolynomial.finSuccEquiv R n) (rothMvHasse (i.cons a) P)).coeff k =
      rothMvHasse i
        ((Polynomial.hasseDeriv a ((MvPolynomial.finSuccEquiv R n) P)).coeff k) := by
  ext l
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [show (i.cons a : RothMvIndex (n + 1)) = Finsupp.cons a i from rfl]
  rw [show (l.cons k : RothMvIndex (n + 1)) = Finsupp.cons k l from rfl]
  rw [rothMvHasse_coeff, rothMvHasse_coeff, Polynomial.hasseDeriv_coeff]
  simp only [Fin.prod_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ,
    Finsupp.add_apply]
  rw [show (↑((k + a).choose a) : MvPolynomial (Fin n) R) =
    MvPolynomial.C ((k + a).choose a : R) by simp]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.finSuccEquiv_coeff_coeff]
  have hcons : Finsupp.cons k l + Finsupp.cons a i = Finsupp.cons (k + a) (l + i) := by
    ext h
    refine Fin.cases ?_ (fun h ↦ ?_) h <;> simp
  rw [hcons]
  ac_rfl

private theorem rothTranslate_eval_coeff {R : Type*} [CommRing R] {m : ℕ}
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

private theorem rothTranslate_coeff_eq_eval_hasse {R : Type*} [CommRing R] :
    ∀ {m : ℕ} (x : Fin m → R) (P : MvPolynomial (Fin m) R) (i : RothMvIndex m),
      (rothTranslate m x P).coeff i = MvPolynomial.eval x (rothMvHasse i P) := by
  intro m
  induction m with
  | zero =>
      intro x P i
      have hx : x = 0 := Subsingleton.elim _ _
      have hi : i = 0 := Subsingleton.elim _ _
      subst x
      subst i
      rw [rothMvHasse_zero_index]
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
        rw [hAk, rothMvHasse_zero] at hBk
        exact (Polynomial.mem_support_iff.mp hk) hBk
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

noncomputable def rothMvWeight {m : ℕ} (r : Fin m → ℕ)
    (i : RothMvIndex m) : ℝ :=
  ∑ h, (i h : ℝ) / r h

private theorem rothMvWeight_add {m : ℕ} (r : Fin m → ℕ) (i j : RothMvIndex m) :
    rothMvWeight r (i + j) = rothMvWeight r i + rothMvWeight r j := by
  simp only [rothMvWeight, Finsupp.add_apply, Nat.cast_add, add_div,
    Finset.sum_add_distrib]

private theorem rothMvWeight_nonneg {m : ℕ} (r : Fin m → ℕ) (i : RothMvIndex m) :
    0 ≤ rothMvWeight r i := by
  unfold rothMvWeight
  positivity

private theorem rothMvWeight_mul {m k : ℕ} (r : Fin m → ℕ) (i : RothMvIndex m)
    (hk : 0 < k) (hr : ∀ h, 0 < r h) :
    rothMvWeight (fun h ↦ k * r h) i = rothMvWeight r i / k := by
  unfold rothMvWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _hh
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hrR : (r h : ℝ) ≠ 0 := by exact_mod_cast (hr h).ne'
  push_cast
  field_simp

noncomputable def rothRidoutComplement {m : ℕ} (r : Fin m → ℕ)
    (i : RothMvIndex m) : RothMvIndex m :=
  Finsupp.equivFunOnFinite.symm fun h ↦ r h - i h

def rothMvVanishesBelow {m : ℕ} {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin m) R) (x : Fin m → R) (r : Fin m → ℕ) (t : ℝ) : Prop :=
  ∀ i, rothMvWeight r i < t → (rothTranslate m x P).coeff i = 0

private theorem rothMvVanishesBelow_hasse {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) (i : RothMvIndex m) :
    rothMvVanishesBelow (rothMvHasse i P) x r (t - rothMvWeight r i) := by
  intro j hj
  rw [rothTranslate_coeff_eq_eval_hasse, rothMvHasse_comp]
  have hw : rothMvWeight r (i + j) < t := by
    rw [rothMvWeight_add]
    linarith
  have hz := hP (i + j) hw
  rw [rothTranslate_coeff_eq_eval_hasse] at hz
  simp [hz]

private theorem rothMvVanishesBelow_mul {m : ℕ} {R : Type*} [CommRing R]
    {P Q : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
    (hP : rothMvVanishesBelow P x r a) (hQ : rothMvVanishesBelow Q x r b) :
    rothMvVanishesBelow (P * Q) x r (a + b) := by
  classical
  intro i hi
  rw [map_mul, ← MvPolynomial.notMem_support_iff]
  intro himem
  have hadd := MvPolynomial.support_mul
    (rothTranslate m x P) (rothTranslate m x Q) himem
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hadd
  have hPu : (rothTranslate m x P).coeff u ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hu
  have hQv : (rothTranslate m x Q).coeff v ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hv
  have hwu : a ≤ rothMvWeight r u := by
    by_contra hnot
    exact hPu (hP u (lt_of_not_ge hnot))
  have hwv : b ≤ rothMvWeight r v := by
    by_contra hnot
    exact hQv (hQ v (lt_of_not_ge hnot))
  rw [← huv, rothMvWeight_add] at hi
  linarith

private theorem rothMvVanishesBelow_zero {m : ℕ} {R : Type*} [CommRing R]
    (x : Fin m → R) (r : Fin m → ℕ) (t : ℝ) :
  rothMvVanishesBelow (0 : MvPolynomial (Fin m) R) x r t := by
  intro i _hi
  simp

private theorem rothMvVanishesBelow_nonpos {m : ℕ} {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin m) R) (x : Fin m → R) (r : Fin m → ℕ)
    {t : ℝ} (ht : t ≤ 0) : rothMvVanishesBelow P x r t := by
  intro i hi
  exact (not_lt_of_ge (rothMvWeight_nonneg r i) (hi.trans_le ht)).elim

private theorem rothMvVanishesBelow_add {m : ℕ} {R : Type*} [CommRing R]
    {P Q : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) (hQ : rothMvVanishesBelow Q x r t) :
  rothMvVanishesBelow (P + Q) x r t := by
  intro i hi
  rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP i hi, hQ i hi, add_zero]

private theorem rothMvVanishesBelow_neg {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) :
    rothMvVanishesBelow (-P) x r t := by
  intro i hi
  rw [map_neg, MvPolynomial.coeff_neg, hP i hi, neg_zero]

private theorem rothMvVanishesBelow_smul {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) (c : R) :
    rothMvVanishesBelow (c • P) x r t := by
  rw [MvPolynomial.smul_eq_C_mul]
  intro i hi
  rw [map_mul, rothTranslate_C]
  simp [hP i hi]

private theorem rothMvVanishesBelow_mono {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
    (hP : rothMvVanishesBelow P x r a) (hba : b ≤ a) :
    rothMvVanishesBelow P x r b := by
  intro i hi
  exact hP i (hi.trans_le hba)

private theorem rothMvVanishesBelow_max {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
    (ha : rothMvVanishesBelow P x r a) (hb : rothMvVanishesBelow P x r b) :
    rothMvVanishesBelow P x r (max a b) := by
  rcases le_total a b with hab | hba
  · simpa [max_eq_right hab] using hb
  · simpa [max_eq_left hba] using ha

private theorem rothMvVanishesBelow_mul_weights {m k : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) (hk : 0 < k) (hr : ∀ h, 0 < r h) :
    rothMvVanishesBelow P x (fun h ↦ k * r h) (t / k) := by
  intro i hi
  apply hP i
  rw [rothMvWeight_mul r i hk hr] at hi
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast hk)).mp hi

private theorem rothMvVanishesBelow_finset_sum {m : ℕ} {R : Type*} [CommRing R]
    {J : Type*} (s : Finset J) {P : J → MvPolynomial (Fin m) R}
    {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : ∀ j ∈ s, rothMvVanishesBelow (P j) x r t) :
    rothMvVanishesBelow (∑ j ∈ s, P j) x r t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rothMvVanishesBelow_zero x r t
  | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs]
      exact rothMvVanishesBelow_add (hP j (Finset.mem_insert_self _ _))
        (ih fun k hk ↦ hP k (Finset.mem_insert_of_mem hk))

private theorem rothMvVanishesBelow_finset_prod {m : ℕ} {R : Type*} [CommRing R]
    {J : Type*} (s : Finset J) (P : J → MvPolynomial (Fin m) R)
    (a : J → ℝ) {x : Fin m → R} {r : Fin m → ℕ}
    (hP : ∀ j ∈ s, rothMvVanishesBelow (P j) x r (a j)) :
    rothMvVanishesBelow (∏ j ∈ s, P j) x r (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro i hi
      simp only [Finset.prod_empty, map_one]
      have hneg : rothMvWeight r i < 0 := hi
      have hnonneg : 0 ≤ rothMvWeight r i := by
        unfold rothMvWeight
        positivity
      exact (not_lt_of_ge hnonneg hneg).elim
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs, Finset.sum_insert hjs]
      exact rothMvVanishesBelow_mul (hP j (Finset.mem_insert_self _ _))
        (ih fun k hk ↦ hP k (Finset.mem_insert_of_mem hk))

noncomputable def rothHasseDet {m k : ℕ} {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin m) R) (u v : Fin k → RothMvIndex m) :
    MvPolynomial (Fin m) R :=
  Matrix.det fun s t ↦ rothMvHasse (u s + v t) P

private theorem rothHasseDet_map {m k : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S)
    (P : MvPolynomial (Fin m) R) (u v : Fin k → RothMvIndex m) :
    MvPolynomial.map f (rothHasseDet P u v) =
      rothHasseDet (MvPolynomial.map f P) u v := by
  classical
  let M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) R) :=
    fun s t ↦ rothMvHasse (u s + v t) P
  unfold rothHasseDet
  change MvPolynomial.map f M.det = _
  rw [RingHom.map_det]
  congr 1
  funext s t
  exact rothMvHasse_map f (u s + v t) P

private theorem rothHasseDet_vanishesBelow_of_rowWeight_le
    {m k : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {T ρ : ℝ}
    (hP : rothMvVanishesBelow P x r T) (u v : Fin k → RothMvIndex m)
    (hu : ∀ s, rothMvWeight r (u s) ≤ ρ) :
    rothMvVanishesBelow (rothHasseDet P u v) x r
      (∑ t, max 0 (T - ρ - rothMvWeight r (v t))) := by
  classical
  unfold rothHasseDet
  let M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) R) :=
    fun s t ↦ rothMvHasse (u s + v t) P
  change rothMvVanishesBelow M.det x r _
  rw [Matrix.det_apply M]
  apply rothMvVanishesBelow_finset_sum
  intro σ _hσ
  have hentry : ∀ s : Fin k,
      rothMvVanishesBelow (rothMvHasse (u (σ s) + v s) P) x r
        (max 0 (T - ρ - rothMvWeight r (v s))) := by
    intro s
    have hder := rothMvVanishesBelow_hasse hP (u (σ s) + v s)
    have hzero := rothMvVanishesBelow_nonpos
      (rothMvHasse (u (σ s) + v s) P) x r (le_refl 0)
    apply rothMvVanishesBelow_mono (rothMvVanishesBelow_max hzero hder)
    rw [rothMvWeight_add]
    exact max_le_max le_rfl (by linarith [hu (σ s)])
  have hprod := rothMvVanishesBelow_finset_prod Finset.univ
    (fun s : Fin k ↦ rothMvHasse (u (σ s) + v s) P)
    (fun s ↦ max 0 (T - ρ - rothMvWeight r (v s)))
    (fun s _hs ↦ hentry s)
  obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
  · simpa [M, hsign] using hprod
  · simpa [M, hsign] using rothMvVanishesBelow_neg hprod

private theorem roth_exists_row_det_ne_zero_of_mem_span {k : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin k) (Fin k) K) (i : Fin k) (S : Set (Fin k → K))
    (hA : A.det ≠ 0) (hi : A i ∈ Submodule.span K S) :
    ∃ v ∈ S, (A.updateRow i v).det ≠ 0 := by
  classical
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hall : ∀ v ∈ Submodule.span K S, (A.updateRow i v).det = 0 := by
    intro v hv
    apply Submodule.span_induction (R := K) (s := S)
      (p := fun v _ ↦ (A.updateRow i v).det = 0)
    · intro v hv
      exact h v hv
    · apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      simp [Matrix.updateRow_apply]
    · intro u v _hu _hv hu hv
      rw [Matrix.det_updateRow_add, hu, hv, add_zero]
    · intro c v _hv hv
      rw [Matrix.det_updateRow_smul, hv, mul_zero]
    · exact hv
  have := hall (A i) hi
  rw [Matrix.updateRow_eq_self] at this
  exact hA this

private theorem roth_exists_nonsingular_rows_of_mem_span {k : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin k) (Fin k) K) (S : Fin k → Set (Fin k → K))
    (hA : A.det ≠ 0) (hspan : ∀ i, A i ∈ Submodule.span K (S i)) :
    ∃ B : Matrix (Fin k) (Fin k) K, B.det ≠ 0 ∧ ∀ i, B i ∈ S i := by
  classical
  have aux : ∀ s : Finset (Fin k),
      ∃ B : Matrix (Fin k) (Fin k) K, B.det ≠ 0 ∧
        (∀ i ∈ s, B i ∈ S i) ∧ (∀ i ∉ s, B i = A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨A, hA, by simp, by simp⟩
    | @insert i s his ih =>
        obtain ⟨B, hB, hBs, hBout⟩ := ih
        have hBi : B i ∈ Submodule.span K (S i) := by
          rw [hBout i his]
          exact hspan i
        obtain ⟨v, hv, hBv⟩ :=
          roth_exists_row_det_ne_zero_of_mem_span B i (S i) hB hBi
        refine ⟨B.updateRow i v, hBv, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · simpa using hv
          · have hji : j ≠ i := by
              intro hji
              subst j
              exact his hjs
            rw [Matrix.updateRow_ne hji]
            exact hBs j hjs
        · intro j hj
          have hji : j ≠ i := by
            intro hji
            subst j
            exact hj (Finset.mem_insert_self i s)
          rw [Matrix.updateRow_ne hji]
          exact hBout j (fun hjs ↦ hj (Finset.mem_insert_of_mem hjs))
  obtain ⟨B, hB, hrows, _⟩ := aux Finset.univ
  exact ⟨B, hB, fun i ↦ hrows i (Finset.mem_univ i)⟩

private theorem roth_wronskian_ne_zero_of_natDegree_ne {K : Type*} [Field K] [CharZero K]
    {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hdeg : f.natDegree ≠ g.natDegree) :
    Polynomial.wronskian f g ≠ 0 := by
  intro hw
  unfold Polynomial.wronskian at hw
  by_cases hfdeg : f.natDegree = 0
  · have hgdeg : g.natDegree ≠ 0 := by aesop
    have hfd : f.derivative = 0 := Polynomial.derivative_eq_zero.mpr hfdeg
    rw [hfd, zero_mul, sub_zero] at hw
    exact mul_ne_zero hf (Polynomial.derivative_ne_zero.mpr hgdeg) hw
  · by_cases hgdeg : g.natDegree = 0
    · have hgd : g.derivative = 0 := Polynomial.derivative_eq_zero.mpr hgdeg
      rw [hgd, mul_zero, zero_sub] at hw
      exact neg_ne_zero.mpr (mul_ne_zero (Polynomial.derivative_ne_zero.mpr hfdeg) hg) hw
    · have hfd : f.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hfdeg
      have hgd : g.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hgdeg
      have hdegrees : (f * g.derivative).degree = (f.derivative * g).degree := by
        rw [Polynomial.degree_eq_natDegree (mul_ne_zero hf hgd),
          Polynomial.degree_eq_natDegree (mul_ne_zero hfd hg),
          Polynomial.natDegree_mul hf hgd, Polynomial.natDegree_mul hfd hg,
          Polynomial.natDegree_derivative, Polynomial.natDegree_derivative]
        norm_cast
        omega
      have hlc : (f * g.derivative).leadingCoeff ≠
          (f.derivative * g).leadingCoeff := by
        simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_derivative]
        intro heq
        have hflc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
        have hglc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg
        apply hdeg
        apply Nat.cast_injective (R := K)
        have heq' : f.leadingCoeff * g.leadingCoeff * (g.natDegree : K) =
            f.leadingCoeff * g.leadingCoeff * (f.natDegree : K) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using heq
        exact (mul_left_cancel₀ (mul_ne_zero hflc hglc)) heq'.symm
      have hlead := Polynomial.leadingCoeff_sub_of_degree_eq hdegrees hlc
      rw [hw, Polynomial.leadingCoeff_zero] at hlead
      exact sub_ne_zero.mpr hlc hlead.symm

private theorem roth_wronskian_eq_zero_imp_eq_smul {K : Type*} [Field K] [CharZero K]
    {f g : K[X]} (hf : f ≠ 0) (hw : Polynomial.wronskian f g = 0) :
    ∃ c : K, g = c • f := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg]⟩
  have hdeg : f.natDegree = g.natDegree := by
    by_contra hne
    exact roth_wronskian_ne_zero_of_natDegree_ne hf hg hne hw
  let c := g.leadingCoeff / f.leadingCoeff
  let h := g - c • f
  have hdegree : h.degree < f.degree := by
    have hc : c ≠ 0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg)
      (Polynomial.leadingCoeff_ne_zero.mpr hf)
    have hcf : c • f ≠ 0 := smul_ne_zero hc hf
    have hlt : h.degree < g.degree := by
      apply Polynomial.degree_sub_lt_left
      · rw [Polynomial.degree_eq_natDegree hg, Polynomial.degree_eq_natDegree hcf]
        rw [Polynomial.natDegree_smul f hc]
        exact_mod_cast hdeg.symm
      · exact hg
      · dsimp [c]
        rw [Polynomial.leadingCoeff_smul_of_smul_regular f
          (IsSMulRegular.of_ne_zero hc : IsSMulRegular K c)]
        simp only [smul_eq_mul]
        exact (div_mul_cancel₀ g.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hf)).symm
    simpa [Polynomial.degree_eq_natDegree hf, Polynomial.degree_eq_natDegree hg, hdeg] using hlt
  have hwr : Polynomial.wronskian f h = 0 := by
    dsimp [h]
    unfold Polynomial.wronskian
    simp only [Polynomial.derivative_sub, Polynomial.derivative_smul]
    unfold Polynomial.wronskian at hw
    simp only [Polynomial.smul_eq_C_mul]
    calc
      f * (g.derivative - Polynomial.C c * f.derivative) -
          f.derivative * (g - Polynomial.C c * f) =
          f * g.derivative - f.derivative * g := by ring
      _ = 0 := hw
  have hh : h = 0 := by
    by_contra hh
    have hnd : f.natDegree ≠ h.natDegree := by
      intro heq
      have := hdegree
      rw [Polynomial.degree_eq_natDegree hf, Polynomial.degree_eq_natDegree hh, heq] at this
      exact lt_irrefl _ this
    exact roth_wronskian_ne_zero_of_natDegree_ne hf hh hnd hwr
  exact ⟨c, sub_eq_zero.mp hh⟩

noncomputable def rothPolyDerivativeRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) (n : ℕ) : Fin k → K[X] :=
  fun j ↦ Polynomial.derivative^[n] (f j)

def rothPolyJetRows {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) (s : ℕ) : Set (Fin k → K[X]) :=
  {v | ∃ n ≤ s, v = rothPolyDerivativeRow f n}

noncomputable def rothPolyRowDerivative {k : ℕ} {K : Type*} [Field K]
    (v : Fin k → K[X]) : Fin k → K[X] :=
  fun j ↦ (v j).derivative

private theorem rothPolyJetRows_mono {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) {s t : ℕ} (hst : s ≤ t) :
    rothPolyJetRows f s ⊆ rothPolyJetRows f t := by
  rintro v ⟨n, hn, rfl⟩
  exact ⟨n, hn.trans hst, rfl⟩

private theorem rothPolyRowDerivative_derivativeRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) (n : ℕ) :
    rothPolyRowDerivative (rothPolyDerivativeRow f n) = rothPolyDerivativeRow f (n + 1) := by
  ext j
  simp only [rothPolyRowDerivative, rothPolyDerivativeRow]
  rw [Function.iterate_succ_apply']

private theorem rothPolyRowDerivative_mem_span {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) {s : ℕ} {v : Fin k → K[X]}
    (hv : v ∈ Submodule.span K[X] (rothPolyJetRows f s)) :
    rothPolyRowDerivative v ∈ Submodule.span K[X] (rothPolyJetRows f (s + 1)) := by
  let T := Submodule.span K[X] (rothPolyJetRows f (s + 1))
  have hold : Submodule.span K[X] (rothPolyJetRows f s) ≤ T :=
    Submodule.span_mono (rothPolyJetRows_mono f (Nat.le_succ s))
  apply Submodule.span_induction (R := K[X]) (s := rothPolyJetRows f s)
    (p := fun v _ ↦ rothPolyRowDerivative v ∈ T)
  · rintro _ ⟨n, hn, rfl⟩
    rw [rothPolyRowDerivative_derivativeRow]
    exact Submodule.subset_span ⟨n + 1, Nat.add_le_add_right hn 1, rfl⟩
  · have hz : rothPolyRowDerivative (0 : Fin k → K[X]) = 0 := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hz]
    exact T.zero_mem
  · intro u w hu hw hu' hw'
    have hadd : rothPolyRowDerivative (u + w) =
        rothPolyRowDerivative u + rothPolyRowDerivative w := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hadd]
    exact T.add_mem hu' hw'
  · intro c w hw hw'
    have hwT : w ∈ T := hold hw
    have hsum : Polynomial.derivative c • w + c • rothPolyRowDerivative w ∈ T :=
      T.add_mem (T.smul_mem _ hwT) (T.smul_mem _ hw')
    convert hsum using 1
    ext j
    simp [rothPolyRowDerivative, Polynomial.derivative_mul]
  · exact hv

noncomputable def rothPolyWronskianRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) : Fin (k + 1) → K[X] :=
  fun j ↦ Polynomial.wronskian (f 0) (f j)

noncomputable def rothPolyWronskianDerivativeRow {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) (n : ℕ) : Fin (k + 1) → K[X] :=
  fun j ↦ Polynomial.derivative^[n] (Polynomial.wronskian (f 0) (f j))

private theorem rothPolyWronskianDerivativeRow_zero {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) (n : ℕ) :
    rothPolyWronskianDerivativeRow f n 0 = 0 := by
  change Polynomial.derivative^[n] (Polynomial.wronskian (f 0) (f 0)) = 0
  rw [Polynomial.wronskian_self_eq_zero]
  simp

private theorem rothPolyWronskianRow_mem_span {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) :
    rothPolyWronskianRow f ∈ Submodule.span K[X] (rothPolyJetRows f 1) := by
  have h0 : rothPolyDerivativeRow f 0 ∈
      Submodule.span K[X] (rothPolyJetRows f 1) :=
    Submodule.subset_span ⟨0, by omega, rfl⟩
  have h1 : rothPolyDerivativeRow f 1 ∈
      Submodule.span K[X] (rothPolyJetRows f 1) :=
    Submodule.subset_span ⟨1, le_rfl, rfl⟩
  have hmem := (Submodule.span K[X] (rothPolyJetRows f 1)).sub_mem
    ((Submodule.span K[X] (rothPolyJetRows f 1)).smul_mem (f 0) h1)
    ((Submodule.span K[X] (rothPolyJetRows f 1)).smul_mem (f 0).derivative h0)
  convert hmem using 1
  ext j
  simp [rothPolyWronskianRow, rothPolyDerivativeRow, Polynomial.wronskian]

private theorem rothPolyWronskianDerivativeRow_mem_span {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) (n : ℕ) :
    rothPolyWronskianDerivativeRow f n ∈
      Submodule.span K[X] (rothPolyJetRows f (n + 1)) := by
  induction n with
  | zero =>
      change rothPolyWronskianRow f ∈ Submodule.span K[X] (rothPolyJetRows f 1)
      exact rothPolyWronskianRow_mem_span f
  | succ n ih =>
      have hder := rothPolyRowDerivative_mem_span f ih
      convert hder using 1
      · ext j
        simp only [rothPolyRowDerivative, rothPolyWronskianDerivativeRow]
        rw [Function.iterate_succ_apply']

private theorem rothPolyWronskian_tail_linearIndependent {k : ℕ} {K : Type*}
    [Field K] [CharZero K] (f : Fin (k + 1) → K[X]) (hf : LinearIndependent K f) :
    LinearIndependent K (fun j : Fin k ↦ Polynomial.wronskian (f 0) (f j.succ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let h : K[X] := ∑ j, c j • f j.succ
  have hwr : Polynomial.wronskian (f 0) h = 0 := by
    calc
      Polynomial.wronskian (f 0) h =
          ∑ j, c j • Polynomial.wronskian (f 0) (f j.succ) := by
        simp [h, ← Polynomial.wronskianBilin_apply]
      _ = 0 := hc
  obtain ⟨a, ha⟩ := roth_wronskian_eq_zero_imp_eq_smul (hf.ne_zero 0) hwr
  let d : Fin (k + 1) → K := Fin.cons (-a) (fun i ↦ c i)
  have hrel : ∑ i, d i • f i = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [d, Fin.cons_zero, Fin.cons_succ]
    change (-a) • f 0 + h = 0
    rw [ha]
    simp
  have hz := Fintype.linearIndependent_iff.mp hf d hrel j.succ
  simpa [d] using hz

private theorem roth_exists_poly_adapted_matrix {K : Type*} [Field K] [CharZero K] :
    ∀ {k : ℕ} (f : Fin k → K[X]), LinearIndependent K f →
      ∃ A : Matrix (Fin k) (Fin k) K[X], A.det ≠ 0 ∧
        ∀ s : Fin k, A s ∈ Submodule.span K[X] (rothPolyJetRows f s) := by
  intro k
  induction k with
  | zero =>
      intro f _hf
      refine ⟨0, by simp, ?_⟩
      exact fun s ↦ Fin.elim0 s
  | succ k ih =>
      intro f hf
      let g : Fin k → K[X] :=
        fun j ↦ Polynomial.wronskian (f 0) (f j.succ)
      have hg : LinearIndependent K g := by
        exact rothPolyWronskian_tail_linearIndependent f hf
      obtain ⟨A, hA, hArows⟩ := ih g hg
      let B : Matrix (Fin (k + 1)) (Fin (k + 1)) K[X] :=
        Fin.cases f (fun s ↦ Fin.cons 0 (A s))
      have hBdet : B.det = f 0 * A.det := by
        rw [Matrix.det_succ_column_zero]
        rw [Fin.sum_univ_succ]
        simp [B, Matrix.submatrix, hf.ne_zero 0]
        rfl
      have hB : B.det ≠ 0 := by
        rw [hBdet]
        exact mul_ne_zero (hf.ne_zero 0) hA
      refine ⟨B, hB, ?_⟩
      intro s
      refine Fin.cases ?_ (fun t ↦ ?_) s
      · change f ∈ Submodule.span K[X] (rothPolyJetRows f 0)
        apply Submodule.subset_span
        refine ⟨0, le_rfl, ?_⟩
        ext j
        simp [rothPolyDerivativeRow]
      · change Fin.cons 0 (A t) ∈
          Submodule.span K[X] (rothPolyJetRows f t.succ)
        let T := Submodule.span K[X] (rothPolyJetRows f t.succ)
        apply Submodule.span_induction (R := K[X]) (s := rothPolyJetRows g t)
          (p := fun v _ ↦ Fin.cons 0 v ∈ T)
        · rintro _ ⟨n, hn, rfl⟩
          have heq : Fin.cons 0 (rothPolyDerivativeRow g n) =
              rothPolyWronskianDerivativeRow f n := by
            ext j
            refine Fin.cases ?_ (fun u ↦ ?_) j
            · simp [rothPolyWronskianDerivativeRow_zero]
            · simp [rothPolyDerivativeRow, rothPolyWronskianDerivativeRow, g]
          rw [heq]
          exact Submodule.span_mono (rothPolyJetRows_mono f (Nat.add_le_add_right hn 1))
            (rothPolyWronskianDerivativeRow_mem_span f n)
        · have hz : (Fin.cons (0 : K[X]) (0 : Fin k → K[X]) :
              Fin (k + 1) → K[X]) = 0 := by
            ext j
            refine Fin.cases (by simp) (fun w ↦ by simp) j
          rw [hz]
          exact T.zero_mem
        · intro u v _hu _hv hu hv
          have hadd : (Fin.cons (0 : K[X]) (u + v) : Fin (k + 1) → K[X]) =
              Fin.cons 0 u + Fin.cons 0 v := by
            ext j
            refine Fin.cases (by simp) (fun w ↦ by simp) j
          rw [hadd]
          exact T.add_mem hu hv
        · intro c v _hv hv
          have hsmul : (Fin.cons (0 : K[X]) (c • v) : Fin (k + 1) → K[X]) =
              c • Fin.cons 0 v := by
            ext j
            refine Fin.cases (by simp) (fun w ↦ by simp) j
          rw [hsmul]
          exact T.smul_mem c hv
        · exact hArows t

private theorem roth_exists_poly_wronskian_orders {k : ℕ} {K : Type*}
    [Field K] [CharZero K] (f : Fin k → K[X]) (hf : LinearIndependent K f) :
    ∃ n : Fin k → ℕ, (∀ s, n s ≤ s) ∧
      (Matrix.det fun s j ↦ Polynomial.derivative^[n s] (f j)) ≠ 0 := by
  classical
  obtain ⟨A, hA, hArows⟩ := roth_exists_poly_adapted_matrix f hf
  obtain ⟨B, hB, hBrows⟩ :=
    roth_exists_nonsingular_rows_of_mem_span A (fun s ↦ rothPolyJetRows f s)
      hA hArows
  choose n hn hrow using hBrows
  refine ⟨n, hn, ?_⟩
  have hBeq : B = fun s j ↦ Polynomial.derivative^[n s] (f j) := by
    ext s j
    rw [hrow s]
    rfl
  rwa [← hBeq]

private theorem roth_poly_wronskian_ne_zero {k : ℕ} {K : Type*}
    [Field K] [CharZero K] (f : Fin k → K[X]) (hf : LinearIndependent K f) :
    (Matrix.det fun s j ↦ Polynomial.derivative^[s.val] (f j)) ≠ 0 := by
  obtain ⟨n, hn, hdet⟩ := roth_exists_poly_wronskian_orders f hf
  have hninj : Function.Injective n := by
    intro s t hst
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_row_eq hne
    ext j
    rw [hst]
  have hnid : ∀ s : Fin k, n s = s.val := by
    cases k with
    | zero => exact fun s ↦ Fin.elim0 s
    | succ k =>
        have hprefix : ∀ s : Fin (k + 1), ∀ t : Fin (k + 1), t.val ≤ s.val → n t = t.val := by
          intro s
          induction s using Fin.induction with
          | zero =>
              intro t ht
              have htval : t.val = 0 := Nat.eq_zero_of_le_zero (by simpa using ht)
              have ht0 : t = 0 := Fin.eq_of_val_eq htval
              subst t
              exact Nat.eq_zero_of_le_zero (hn 0)
          | succ s ih =>
              intro t ht
              by_cases hts : t = s.succ
              · subst t
                apply Nat.le_antisymm (hn s.succ)
                by_contra hnot
                have hlt : n s.succ < s.succ.val := Nat.lt_of_not_ge hnot
                let u : Fin (k + 1) := ⟨n s.succ, hlt.trans s.succ.isLt⟩
                have hu : u.val ≤ s.castSucc.val := by
                  dsimp [u]
                  simpa using Nat.le_pred_of_lt hlt
                have hnu := ih u hu
                have hcollision : n u = n s.succ := by simpa [u] using hnu
                have hus := hninj hcollision
                have := congrArg Fin.val hus
                simp [u] at this
                omega
              · apply ih t
                have hlt : t.val < s.succ.val := lt_of_le_of_ne ht (by
                  intro heq
                  apply hts
                  exact Fin.eq_of_val_eq heq)
                simpa using Nat.le_pred_of_lt hlt
        exact fun s ↦ hprefix s s le_rfl
  simpa only [hnid] using hdet

private theorem roth_poly_hasse_wronskian_ne_zero {k : ℕ}
    (f : Fin k → ℚ[X]) (hf : LinearIndependent ℚ f) :
    (Matrix.det fun s j ↦ Polynomial.hasseDeriv s.val (f j)) ≠ 0 := by
  let A : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ Polynomial.derivative^[s.val] (f j)
  let H : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ Polynomial.hasseDeriv s.val (f j)
  have hder : A.det ≠ 0 := roth_poly_wronskian_ne_zero f hf
  intro hhasse
  apply hder
  have hhasse' : H.det = 0 := hhasse
  have heq : A.det =
      Polynomial.C (∏ s : Fin k, (s.val.factorial : ℚ)) * H.det := by
    classical
    rw [Matrix.det_apply A, Matrix.det_apply H, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _hσ
    have hprod : ∏ s, A (σ s) s =
        Polynomial.C (∏ s : Fin k, (s.val.factorial : ℚ)) * ∏ s, H (σ s) s := by
      have hfactor : (∏ s : Fin k, ((σ s).val.factorial : ℚ)) =
          ∏ s : Fin k, (s.val.factorial : ℚ) :=
        Equiv.prod_comp σ (fun s : Fin k ↦ (s.val.factorial : ℚ))
      dsimp [A, H]
      rw [← hfactor, map_prod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro s _hs
      have hfac :=
        congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℚ) (σ s).val) (f s)
      simpa [smul_eq_mul] using hfac.symm
    rw [hprod]
    obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
    · simp [hsign]
    · simp [hsign]
  rw [heq, hhasse', mul_zero]

def rothKroneckerEncode {m : ℕ} (D : ℕ) (i : Fin m → ℕ) : ℕ :=
  ∑ h : Fin m, i h * D ^ (h : ℕ)

private theorem rothKroneckerEncode_succ {m D : ℕ} (i : Fin (m + 1) → ℕ) :
    rothKroneckerEncode D i =
      i 0 + D * rothKroneckerEncode D (fun h ↦ i h.succ) := by
  rw [rothKroneckerEncode, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, rothKroneckerEncode, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _hh
  simp [mul_left_comm, mul_comm]

private theorem rothKroneckerEncode_injective : ∀ {m D : ℕ}, 1 < D →
    ∀ {i j : Fin m → ℕ}, (∀ h, i h < D) → (∀ h, j h < D) →
      rothKroneckerEncode D i = rothKroneckerEncode D j → i = j := by
  intro m
  induction m with
  | zero =>
      intro D _hD i j _hi _hj _heq
      funext h
      exact Fin.elim0 h
  | succ m ih =>
      intro D hD i j hi hj heq
      rw [rothKroneckerEncode_succ, rothKroneckerEncode_succ] at heq
      have hzero : i 0 = j 0 := by
        have hmod := congrArg (fun n ↦ n % D) heq
        simpa [Nat.mod_eq_of_lt (hi 0), Nat.mod_eq_of_lt (hj 0)] using hmod
      have htailEq : rothKroneckerEncode D (fun (h : Fin m) ↦ i h.succ) =
          rothKroneckerEncode D (fun (h : Fin m) ↦ j h.succ) := by
        rw [hzero] at heq
        exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hD) (Nat.add_left_cancel heq)
      have htail : (fun (h : Fin m) ↦ i h.succ) = fun (h : Fin m) ↦ j h.succ :=
        ih hD (fun (h : Fin m) ↦ hi h.succ) (fun (h : Fin m) ↦ hj h.succ) htailEq
      funext h
      refine Fin.cases hzero (fun t ↦ ?_) h
      exact congrFun htail t

noncomputable def rothKronecker {m : ℕ} {K : Type*} [Field K] (D : ℕ) :
    MvPolynomial (Fin m) K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun h ↦ Polynomial.X ^ D ^ (h : ℕ))

private theorem rothKronecker_monomial {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (i : Fin m →₀ ℕ) (c : K) :
    rothKronecker D (MvPolynomial.monomial i c) =
      Polynomial.monomial (rothKroneckerEncode D fun h ↦ i h) c := by
  rw [rothKronecker, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  congr 1
  unfold rothKroneckerEncode
  calc
    ∑ a ∈ i.support, D ^ (a : ℕ) * i a =
        ∑ a : Fin m, D ^ (a : ℕ) * i a := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ha hnot
      have hai : i a = 0 := by simpa using hnot
      simp [hai]
    _ = ∑ a : Fin m, i a * D ^ (a : ℕ) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact Nat.mul_comm _ _

private theorem rothKronecker_eq_sum {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (P : MvPolynomial (Fin m) K) :
    rothKronecker D P = ∑ i ∈ P.support,
      Polynomial.monomial (rothKroneckerEncode D fun h ↦ i h) (P.coeff i) := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [rothKronecker_monomial]

def rothKroneckerBounded {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (P : MvPolynomial (Fin m) K) : Prop :=
  ∀ i ∈ P.support, ∀ h, i h < D

private theorem rothKronecker_ne_zero_of_bounded {m : ℕ} {K : Type*} [Field K] {D : ℕ}
    (hD : 1 < D) {P : MvPolynomial (Fin m) K} (hP : P ≠ 0)
    (hb : rothKroneckerBounded D P) : rothKronecker D P ≠ 0 := by
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr hP
  have hci : P.coeff i ≠ 0 := MvPolynomial.mem_support_iff.mp hi
  have hcoeff : (rothKronecker D P).coeff (rothKroneckerEncode D fun h ↦ i h) =
      P.coeff i := by
    rw [rothKronecker_eq_sum, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have henc : rothKroneckerEncode D (fun h ↦ j h) ≠
          rothKroneckerEncode D (fun h ↦ i h) := by
        intro heq
        apply hji
        apply Finsupp.ext
        intro h
        exact congrFun (rothKroneckerEncode_injective hD (hb j hj) (hb i hi) heq) h
      simp [henc]
    · exact fun hnot ↦ (hnot hi).elim
  intro hz
  have := congrArg (fun Q : K[X] ↦ Q.coeff (rothKroneckerEncode D fun h ↦ i h)) hz
  rw [hcoeff, Polynomial.coeff_zero] at this
  exact hci this

private theorem rothKroneckerBounded_finset_sum {m : ℕ} {K : Type*} [Field K] {D : ℕ}
    {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (Fin m) K)
    (hP : ∀ a ∈ s, rothKroneckerBounded D (P a)) :
    rothKroneckerBounded D (∑ a ∈ s, P a) := by
  intro i hi h
  by_contra hnot
  have hz : (∑ a ∈ s, P a).coeff i = 0 := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finsupp.notMem_support_iff.mp
    exact fun hia ↦ hnot (hP a ha i hia h)
  exact (MvPolynomial.mem_support_iff.mp hi) hz

private theorem rothKronecker_linearIndependent {m k : ℕ} {K : Type*} [Field K]
    {D : ℕ} (hD : 1 < D) (f : Fin k → MvPolynomial (Fin m) K)
    (hf : LinearIndependent K f) (hb : ∀ j, rothKroneckerBounded D (f j)) :
    LinearIndependent K (fun j ↦ rothKronecker D (f j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let P := ∑ a, c a • f a
  have hmap : rothKronecker D P = 0 := by
    dsimp [P]
    rw [map_sum]
    simpa [Algebra.smul_def, rothKronecker] using hc
  have hPb : rothKroneckerBounded D P := by
    dsimp [P]
    apply rothKroneckerBounded_finset_sum Finset.univ
    intro a _ha i hi h
    by_cases hca : c a = 0
    · simp [hca] at hi
    · have hsupp : (c a • f a).support = (f a).support :=
        MvPolynomial.support_smul_eq hca (f a)
      rw [hsupp] at hi
      exact hb a i hi h
  have hPzero : P = 0 := by
    by_contra hP
    exact rothKronecker_ne_zero_of_bounded hD hP hPb hmap
  exact Fintype.linearIndependent_iff.mp hf c hPzero j

private theorem rothKronecker_X {m : ℕ} {K : Type*} [Field K] (D : ℕ) (h : Fin m) :
    rothKronecker D (MvPolynomial.X h : MvPolynomial (Fin m) K) =
      Polynomial.X ^ D ^ (h : ℕ) := by
  simp [rothKronecker]

private theorem rothKronecker_derivative {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (P : MvPolynomial (Fin m) K) :
    (rothKronecker D P).derivative = ∑ h : Fin m,
      Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
        rothKronecker D (MvPolynomial.pderiv h P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rothKronecker]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h _hh
      ring
  | mul_X P n hP =>
      have hsecond : (∑ h : Fin m,
          Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
            ((rothKronecker D P) *
              rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n)))) =
          Polynomial.C (D ^ (n : ℕ) : K) * Polynomial.X ^ (D ^ (n : ℕ) - 1) *
            rothKronecker D P := by
        rw [Finset.sum_eq_single n]
        · simp [mul_assoc, mul_comm]
        · intro h _hh hne
          rw [MvPolynomial.pderiv_X_of_ne hne.symm]
          simp
        · simp
      rw [map_mul, rothKronecker_X, Polynomial.derivative_mul, hP,
        Polynomial.derivative_X_pow]
      symm
      calc
        (∑ h : Fin m,
            Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
              rothKronecker D (MvPolynomial.pderiv h (P * MvPolynomial.X n))) =
            ∑ h : Fin m,
              (Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  rothKronecker D (MvPolynomial.pderiv h P) *
                    Polynomial.X ^ D ^ (n : ℕ) +
                Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  ((rothKronecker D P) *
                    rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n)))) := by
          apply Finset.sum_congr rfl
          intro h _hh
          rw [MvPolynomial.pderiv_mul]
          simp only [map_add, map_mul, rothKronecker_X]
          ring
        _ = (∑ h : Fin m,
                Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  rothKronecker D (MvPolynomial.pderiv h P) *
                    Polynomial.X ^ D ^ (n : ℕ)) +
              ∑ h : Fin m,
                Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  ((rothKronecker D P) *
                    rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n))) :=
          Finset.sum_add_distrib
        _ = (∑ h : Fin m,
                Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  rothKronecker D (MvPolynomial.pderiv h P)) *
                Polynomial.X ^ D ^ (n : ℕ) +
              Polynomial.C (D ^ (n : ℕ) : K) * Polynomial.X ^ (D ^ (n : ℕ) - 1) *
                rothKronecker D P := by
          rw [← Finset.sum_mul, hsecond]
        _ = _ := by
          push_cast
          ring

private theorem rothMvHasse_single_one {m : ℕ} (h : Fin m)
    (P : MvPolynomial (Fin m) ℚ) :
    rothMvHasse (Finsupp.single h 1) P = MvPolynomial.pderiv h P := by
  ext i
  rw [rothMvHasse_coeff, MvPolynomial.coeff_pderiv]
  have hprod :
      (∏ b : Fin m,
          (Nat.choose ((i + (Finsupp.single h 1 : RothMvIndex m)) b)
            ((Finsupp.single h 1 : RothMvIndex m) b) : ℚ)) =
        (i h + 1 : ℚ) := by
    rw [Finset.prod_eq_single h]
    · simp
    · intro b _hb hbh
      simp [hbh]
    · simp
  rw [hprod]
  ring

private theorem roth_pderiv_hasse {m : ℕ} (h : Fin m) (i : RothMvIndex m)
    (P : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.pderiv h (rothMvHasse i P) =
      (i h + 1 : ℚ) • rothMvHasse (i + Finsupp.single h 1) P := by
  rw [← rothMvHasse_single_one, rothMvHasse_comp]
  have hprod :
      (∏ b : Fin m,
          (Nat.choose ((i + (Finsupp.single h 1 : RothMvIndex m)) b) (i b) : ℚ)) =
        (i h + 1 : ℚ) := by
    rw [Finset.prod_eq_single h]
    · simp
    · intro b _hb hbh
      simp [hbh]
    · simp
  rw [hprod]

def rothMvOrder {m : ℕ} (i : RothMvIndex m) : ℕ :=
  ∑ h, i h

private theorem rothMvOrder_add {m : ℕ} (i j : RothMvIndex m) :
    rothMvOrder (i + j) = rothMvOrder i + rothMvOrder j := by
  simp [rothMvOrder, Finset.sum_add_distrib]

private theorem rothMvOrder_single {m : ℕ} (h : Fin m) (n : ℕ) :
    rothMvOrder (Finsupp.single h n) = n := by
  simp [rothMvOrder]

private theorem rothMvOrder_add_single_one {m : ℕ} (i : RothMvIndex m) (h : Fin m) :
    rothMvOrder (i + Finsupp.single h 1) = rothMvOrder i + 1 := by
  rw [rothMvOrder_add, rothMvOrder_single]

noncomputable def rothKronHasseRow {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (i : RothMvIndex m) : Fin k → ℚ[X] :=
  fun j ↦ rothKronecker D (rothMvHasse i (f j))

def rothKronHasseJetRows {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (s : ℕ) : Set (Fin k → ℚ[X]) :=
  {v | ∃ i : RothMvIndex m, rothMvOrder i ≤ s ∧ v = rothKronHasseRow D f i}

private theorem rothKronHasseJetRows_mono {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) {s t : ℕ} (hst : s ≤ t) :
    rothKronHasseJetRows D f s ⊆ rothKronHasseJetRows D f t := by
  rintro v ⟨i, hi, rfl⟩
  exact ⟨i, hi.trans hst, rfl⟩

private theorem rothKronHasseRow_derivative {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (i : RothMvIndex m) :
    rothPolyRowDerivative (rothKronHasseRow D f i) =
      ∑ h : Fin m,
        (Polynomial.C (D ^ (h : ℕ) : ℚ) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
          Polynomial.C (i h + 1 : ℚ)) •
            rothKronHasseRow D f (i + Finsupp.single h 1) := by
  funext j
  simp only [rothPolyRowDerivative, rothKronHasseRow, Pi.smul_apply,
    Finset.sum_apply]
  rw [rothKronecker_derivative]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [roth_pderiv_hasse]
  simp only [Algebra.smul_def, map_mul]
  simp [rothKronecker]
  ring

private theorem rothKronHasseRowDerivative_mem_span {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) {s : ℕ} {v : Fin k → ℚ[X]}
    (hv : v ∈ Submodule.span ℚ[X] (rothKronHasseJetRows D f s)) :
    rothPolyRowDerivative v ∈
      Submodule.span ℚ[X] (rothKronHasseJetRows D f (s + 1)) := by
  let T := Submodule.span ℚ[X] (rothKronHasseJetRows D f (s + 1))
  have hold : Submodule.span ℚ[X] (rothKronHasseJetRows D f s) ≤ T :=
    Submodule.span_mono (rothKronHasseJetRows_mono D f (Nat.le_succ s))
  apply Submodule.span_induction (R := ℚ[X]) (s := rothKronHasseJetRows D f s)
    (p := fun v _ ↦ rothPolyRowDerivative v ∈ T)
  · rintro _ ⟨i, hi, rfl⟩
    rw [rothKronHasseRow_derivative]
    apply Submodule.sum_mem
    intro h _hh
    apply T.smul_mem
    apply Submodule.subset_span
    refine ⟨i + Finsupp.single h 1, ?_, rfl⟩
    rw [rothMvOrder_add_single_one]
    omega
  · have hz : rothPolyRowDerivative (0 : Fin k → ℚ[X]) = 0 := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hz]
    exact T.zero_mem
  · intro u w _hu _hw hu hw
    have hadd : rothPolyRowDerivative (u + w) =
        rothPolyRowDerivative u + rothPolyRowDerivative w := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hadd]
    exact T.add_mem hu hw
  · intro c w hw hw'
    have hwT : w ∈ T := hold hw
    have hsum : Polynomial.derivative c • w + c • rothPolyRowDerivative w ∈ T :=
      T.add_mem (T.smul_mem _ hwT) (T.smul_mem _ hw')
    convert hsum using 1
    ext j
    simp [rothPolyRowDerivative, Polynomial.derivative_mul]
  · exact hv

private theorem rothPolyDerivativeRow_mem_kronHasse_span {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (s : ℕ) :
    rothPolyDerivativeRow (fun j ↦ rothKronecker D (f j)) s ∈
      Submodule.span ℚ[X] (rothKronHasseJetRows D f s) := by
  induction s with
  | zero =>
      apply Submodule.subset_span
      refine ⟨0, by simp [rothMvOrder], ?_⟩
      ext j
      simp [rothPolyDerivativeRow, rothKronHasseRow, rothMvHasse_zero_index]
  | succ s ih =>
      have hder := rothKronHasseRowDerivative_mem_span D f ih
      rw [rothPolyRowDerivative_derivativeRow] at hder
      simpa [Nat.succ_eq_add_one] using hder

private theorem roth_exists_generalized_wronskian_of_bounded {m k D : ℕ}
    (hD : 1 < D) (f : Fin k → MvPolynomial (Fin m) ℚ)
    (hf : LinearIndependent ℚ f) (hb : ∀ j, rothKroneckerBounded D (f j)) :
    ∃ i : Fin k → RothMvIndex m,
      (∀ s, rothMvOrder (i s) ≤ s) ∧
        (Matrix.det fun s j ↦ rothMvHasse (i s) (f j)) ≠ 0 := by
  classical
  let g : Fin k → ℚ[X] := fun j ↦ rothKronecker D (f j)
  have hg : LinearIndependent ℚ g :=
    rothKronecker_linearIndependent hD f hf hb
  let A : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ Polynomial.derivative^[s.val] (g j)
  have hA : A.det ≠ 0 := roth_poly_wronskian_ne_zero g hg
  have hArows : ∀ s : Fin k,
      A s ∈ Submodule.span ℚ[X] (rothKronHasseJetRows D f s) := by
    intro s
    exact rothPolyDerivativeRow_mem_kronHasse_span D f s
  obtain ⟨B, hB, hBrows⟩ :=
    roth_exists_nonsingular_rows_of_mem_span A
      (fun s ↦ rothKronHasseJetRows D f s) hA hArows
  choose i hi hrow using hBrows
  refine ⟨i, hi, ?_⟩
  let C : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℚ) :=
    fun s j ↦ rothMvHasse (i s) (f j)
  have hBC : B = (rothKronecker D).mapMatrix C := by
    ext s j
    rw [hrow s]
    rfl
  have hmapdet : rothKronecker D C.det = B.det := by
    rw [RingHom.map_det, ← hBC]
  intro hC
  apply hB
  rw [← hmapdet, hC, map_zero]

def rothFinsuppL1 {α : Type*} (f : α →₀ ℤ) : ℕ :=
  ∑ a ∈ f.support, (f a).natAbs

private theorem rothFinsuppL1_sum_superset {α : Type*} (f : α →₀ ℤ) (s : Finset α)
    (hfs : f.support ⊆ s) :
    rothFinsuppL1 f = ∑ a ∈ s, (f a).natAbs := by
  unfold rothFinsuppL1
  apply Finset.sum_subset hfs
  intro a ha hnot
  rw [Finsupp.notMem_support_iff.mp hnot]
  simp

private theorem rothFinsuppL1_add {α : Type*} (f g : α →₀ ℤ) :
    rothFinsuppL1 (f + g) ≤ rothFinsuppL1 f + rothFinsuppL1 g := by
  classical
  let s := f.support ∪ g.support
  rw [rothFinsuppL1_sum_superset (f + g) s Finsupp.support_add]
  rw [rothFinsuppL1_sum_superset f s Finset.subset_union_left]
  rw [rothFinsuppL1_sum_superset g s Finset.subset_union_right]
  rw [← Finset.sum_add_distrib]
  gcongr with a ha
  exact Int.natAbs_add_le _ _

private theorem rothFinsuppL1_neg {α : Type*} (f : α →₀ ℤ) :
    rothFinsuppL1 (-f) = rothFinsuppL1 f := by
  classical
  unfold rothFinsuppL1
  rw [Finsupp.support_neg]
  congr with a
  exact Int.natAbs_neg _

private theorem rothFinsuppL1_single {α : Type*} (a : α) (c : ℤ) :
    rothFinsuppL1 (Finsupp.single a c) = c.natAbs := by
  classical
  by_cases hc : c = 0
  · simp [hc, rothFinsuppL1]
  · simp [rothFinsuppL1, hc]

private theorem rothFinsuppL1_apply_le {α : Type*} (f : α →₀ ℤ) (a : α) :
    (f a).natAbs ≤ rothFinsuppL1 f := by
  classical
  by_cases ha : f a = 0
  · simp [ha]
  · exact Finset.single_le_sum (fun b _hb ↦ Nat.zero_le (f b).natAbs)
      (Finsupp.mem_support_iff.mpr ha)

def rothMvL1 {m : ℕ} (P : MvPolynomial (Fin m) ℤ) : ℕ :=
  rothFinsuppL1 P.coeff

private theorem rothMvL1_coeff_le {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (i : RothMvIndex m) : (P.coeff i).natAbs ≤ rothMvL1 P :=
  rothFinsuppL1_apply_le P.coeff i

private theorem rothMvL1_eq_sum {m : ℕ} (P : MvPolynomial (Fin m) ℤ) :
    rothMvL1 P = ∑ i ∈ P.support, (P.coeff i).natAbs := by
  unfold rothMvL1 rothFinsuppL1
  rw [← MvPolynomial.finsupp_support_eq_support]

private theorem rothMvL1_monomial {m : ℕ} (i : RothMvIndex m) (c : ℤ) :
    rothMvL1 (MvPolynomial.monomial i c) = c.natAbs := by
  change rothFinsuppL1 (Finsupp.single i c) = c.natAbs
  exact rothFinsuppL1_single i c

private theorem rothMvL1_neg {m : ℕ} (P : MvPolynomial (Fin m) ℤ) :
    rothMvL1 (-P) = rothMvL1 P :=
  rothFinsuppL1_neg P.coeff

private theorem rothMvL1_finset_sum {m : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial (Fin m) ℤ) :
    rothMvL1 (∑ a ∈ s, P a) ≤ ∑ a ∈ s, rothMvL1 (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothMvL1, rothFinsuppL1]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (rothFinsuppL1_add _ _).trans (Nat.add_le_add_left ih _)

private theorem rothMvL1_mul {m : ℕ} (P Q : MvPolynomial (Fin m) ℤ) :
    rothMvL1 (P * Q) ≤ rothMvL1 P * rothMvL1 Q := by
  classical
  rw [MvPolynomial.mul_def, Finsupp.sum]
  calc
    rothMvL1 (∑ a ∈ P.support,
        Q.coeff.sum fun b d ↦ MvPolynomial.monomial (a + b) (P.coeff a * d))
        ≤ ∑ a ∈ P.support,
          rothMvL1 (Q.coeff.sum fun b d ↦
            MvPolynomial.monomial (a + b) (P.coeff a * d)) :=
      rothMvL1_finset_sum P.support _
    _ = ∑ a ∈ P.support,
          rothMvL1 (∑ b ∈ Q.support,
            MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      congr with a
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support,
          rothMvL1 (MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      gcongr with a ha
      exact rothMvL1_finset_sum Q.support _
    _ = ∑ a ∈ P.support, (P.coeff a).natAbs * rothMvL1 Q := by
      congr with a
      simp_rw [rothMvL1_monomial, Int.natAbs_mul]
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, ← Finset.mul_sum]
    _ = rothMvL1 P * rothMvL1 Q := by
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, Finset.sum_mul]

private theorem rothMvL1_one {m : ℕ} :
    rothMvL1 (1 : MvPolynomial (Fin m) ℤ) = 1 := by
  rw [show (1 : MvPolynomial (Fin m) ℤ) = MvPolynomial.monomial 0 1 by simp,
    rothMvL1_monomial]
  norm_num

private theorem rothMvL1_finset_prod {m : ℕ} {J : Type*}
    (s : Finset J) (P : J → MvPolynomial (Fin m) ℤ) :
    rothMvL1 (∏ j ∈ s, P j) ≤ ∏ j ∈ s, rothMvL1 (P j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothMvL1_one]
  | @insert j s hjs ih =>
      simp only [Finset.prod_insert hjs]
      exact (rothMvL1_mul _ _).trans (Nat.mul_le_mul_left _ ih)

private theorem rothMvL1_det_le {m k B : ℕ}
    (M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℤ))
    (hM : ∀ s t, rothMvL1 (M s t) ≤ B) :
    rothMvL1 M.det ≤ k.factorial * B ^ k := by
  classical
  rw [Matrix.det_apply]
  calc
    rothMvL1 (∑ σ, Equiv.Perm.sign σ • ∏ i, M (σ i) i) ≤
        ∑ σ ∈ Finset.univ,
          rothMvL1 (Equiv.Perm.sign σ • ∏ i, M (σ i) i) :=
      rothMvL1_finset_sum Finset.univ _
    _ = ∑ σ : Equiv.Perm (Fin k), rothMvL1 (∏ i, M (σ i) i) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
      · simp [hsign]
      · simp [hsign, rothMvL1_neg]
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), B ^ k := by
      gcongr with σ
      calc
        rothMvL1 (∏ i, M (σ i) i) ≤ ∏ i, rothMvL1 (M (σ i) i) :=
          rothMvL1_finset_prod Finset.univ _
        _ ≤ ∏ _i : Fin k, B := by
          gcongr with i
          exact hM (σ i) i
        _ = B ^ k := by simp
    _ = k.factorial * B ^ k := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      rfl

def rothDegreeBound {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (r : Fin m → ℕ) : Prop :=
  ∀ j ∈ P.support, ∀ h, j h ≤ r h

def rothDegreeBoundOver {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) (r : Fin m → ℕ) : Prop :=
  ∀ j ∈ P.support, ∀ h, j h ≤ r h

private theorem rothDegreeBound_add {m : ℕ}
    {P Q : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : rothDegreeBound P r) (hQ : rothDegreeBound Q r) :
    rothDegreeBound (P + Q) r := by
  intro i hi h
  rcases Finset.mem_union.mp (MvPolynomial.support_add hi) with hiP | hiQ
  · exact hP i hiP h
  · exact hQ i hiQ h

private theorem rothDegreeBound_mul {m : ℕ}
    {P Q : MvPolynomial (Fin m) ℤ} {r s : Fin m → ℕ}
    (hP : rothDegreeBound P r) (hQ : rothDegreeBound Q s) :
    rothDegreeBound (P * Q) (fun h ↦ r h + s h) := by
  intro i hi h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hi)
  rw [← huv, Finsupp.add_apply]
  exact Nat.add_le_add (hP u hu h) (hQ v hv h)

private theorem rothDegreeBound_smul {m : ℕ}
    {P : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : rothDegreeBound P r) (c : ℤ) : rothDegreeBound (c • P) r := by
  intro i hi h
  exact hP i (MvPolynomial.support_smul hi) h

private theorem rothDegreeBound_finset_sum {m : ℕ} {J : Type*}
    (s : Finset J) {P : J → MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : ∀ j ∈ s, rothDegreeBound (P j) r) :
    rothDegreeBound (∑ j ∈ s, P j) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothDegreeBound]
  | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs]
      exact rothDegreeBound_add (hP j (Finset.mem_insert_self _ _))
        (ih fun t ht ↦ hP t (Finset.mem_insert_of_mem ht))

private theorem rothDegreeBound_finset_prod {m : ℕ} {J : Type*}
    (s : Finset J) {P : J → MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : ∀ j ∈ s, rothDegreeBound (P j) r) :
    rothDegreeBound (∏ j ∈ s, P j) (fun h ↦ s.card * r h) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro i hi h
      simp only [Finset.card_empty, zero_mul]
      rw [Finset.prod_empty, MvPolynomial.support_one] at hi
      rw [Finset.mem_singleton.mp hi]
      simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs]
      have hmul := rothDegreeBound_mul
        (hP j (Finset.mem_insert_self _ _))
        (ih fun t ht ↦ hP t (Finset.mem_insert_of_mem ht))
      simpa [Finset.card_insert_of_notMem hjs, Nat.add_mul, add_comm] using hmul

private theorem rothDegreeBound_det {m k : ℕ}
    (M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℤ))
    (r : Fin m → ℕ) (hM : ∀ s t, rothDegreeBound (M s t) r) :
    rothDegreeBound M.det (fun h ↦ k * r h) := by
  classical
  rw [Matrix.det_apply]
  apply rothDegreeBound_finset_sum Finset.univ
  intro σ _hσ
  apply rothDegreeBound_smul
  simpa using rothDegreeBound_finset_prod Finset.univ
    (fun t _ht ↦ hM (σ t) t)

private theorem rothDegreeBoundOver_hasse {m : ℕ} {R : Type*} [CommSemiring R]
    {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ} (hP : rothDegreeBoundOver P r)
    (i : RothMvIndex m) :
    rothDegreeBoundOver (rothMvHasse i P) r := by
  intro k hk h
  have hcoeff := MvPolynomial.mem_support_iff.mp hk
  rw [rothMvHasse_coeff] at hcoeff
  have hPk : P.coeff (k + i) ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hz, mul_zero])
  have hmem : k + i ∈ P.support := MvPolynomial.mem_support_iff.mpr hPk
  exact (Nat.le_add_right (k h) (i h)).trans (hP (k + i) hmem h)

private theorem rothHasseDet_degreeBound {m k : ℕ}
    {P : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : rothDegreeBound P r) (u v : Fin k → RothMvIndex m) :
    rothDegreeBound (rothHasseDet P u v) (fun h ↦ k * r h) := by
  apply rothDegreeBound_det
  intro s t
  exact rothDegreeBoundOver_hasse hP (u s + v t)

private theorem rothDegreeBoundOver_map {m : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ} (hP : rothDegreeBoundOver P r) :
    rothDegreeBoundOver (MvPolynomial.map f P) r := by
  intro k hk h
  exact hP k (MvPolynomial.support_map_subset f P hk) h

private theorem roth_exists_generalized_wronskian {m k : ℕ}
    (f : Fin k → MvPolynomial (Fin m) ℚ) (r : Fin m → ℕ)
    (hf : LinearIndependent ℚ f) (hdeg : ∀ j, rothDegreeBoundOver (f j) r) :
    ∃ i : Fin k → RothMvIndex m,
      (∀ s, rothMvOrder (i s) ≤ s) ∧
        (Matrix.det fun s j ↦ rothMvHasse (i s) (f j)) ≠ 0 := by
  classical
  let D := 2 + ∑ h, r h
  have hD : 1 < D := by
    dsimp [D]
    omega
  have hb : ∀ j, rothKroneckerBounded D (f j) := by
    intro j i hi h
    have hir := hdeg j i hi h
    have hrsum : r h ≤ ∑ t, r t := by
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    dsimp [D]
    omega
  exact roth_exists_generalized_wronskian_of_bounded hD f hf hb

noncomputable def rothLastEquiv (R : Type*) [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (MvPolynomial.renameEquiv R finSuccEquivLast).trans
    (MvPolynomial.optionEquivLeft R (Fin n))

private theorem roth_equivMapDomain_symm {A B M : Type*} [Zero M]
    (e : A ≃ B) (d : B →₀ M) :
    Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm d) = d := by
  ext b
  simp [Finsupp.equivMapDomain_apply]

noncomputable def rothLastIndex {n : ℕ} (i : RothMvIndex n) (a : ℕ) :
    RothMvIndex (n + 1) :=
  (Finsupp.equivCongrLeft finSuccEquivLast).symm (Finsupp.optionElim a i)

private theorem rothLastIndex_castSucc {n : ℕ} (i : RothMvIndex n) (a : ℕ)
    (h : Fin n) : rothLastIndex i a h.castSucc = i h := by
  have heq : (Finsupp.equivCongrLeft finSuccEquivLast) (rothLastIndex i a) =
      Finsupp.optionElim a i := by
    simpa [rothLastIndex, Finsupp.equivCongrLeft_apply] using
      roth_equivMapDomain_symm finSuccEquivLast (Finsupp.optionElim a i)
  have := congrArg (fun d : Option (Fin n) →₀ ℕ ↦ d (some h)) heq
  simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using this

private theorem rothLastIndex_last {n : ℕ} (i : RothMvIndex n) (a : ℕ) :
    rothLastIndex i a (Fin.last n) = a := by
  have heq : (Finsupp.equivCongrLeft finSuccEquivLast) (rothLastIndex i a) =
      Finsupp.optionElim a i := by
    simpa [rothLastIndex, Finsupp.equivCongrLeft_apply] using
      roth_equivMapDomain_symm finSuccEquivLast (Finsupp.optionElim a i)
  have := congrArg (fun d : Option (Fin n) →₀ ℕ ↦ d none) heq
  simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using this

noncomputable def rothLastTail {n : ℕ} (d : RothMvIndex (n + 1)) :
    RothMvIndex n :=
  ((Finsupp.equivCongrLeft finSuccEquivLast) d).some

private theorem rothLastTail_apply {n : ℕ} (d : RothMvIndex (n + 1)) (h : Fin n) :
    rothLastTail d h = d h.castSucc := by
  simp [rothLastTail, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply]

private theorem rothLastIndex_eta {n : ℕ} (d : RothMvIndex (n + 1)) :
    rothLastIndex (rothLastTail d) (d (Fin.last n)) = d := by
  ext h
  refine Fin.lastCases ?_ (fun j ↦ ?_) h
  · rw [rothLastIndex_last]
  · rw [rothLastIndex_castSucc, rothLastTail_apply]

private theorem rothLastIndex_left_injective {n : ℕ} (a : ℕ) :
    Function.Injective (fun i : RothMvIndex n ↦ rothLastIndex i a) := by
  intro i j hij
  ext h
  have := congrArg (fun d : RothMvIndex (n + 1) ↦ d h.castSucc) hij
  simpa [rothLastIndex_castSucc] using this

private theorem rothLastIndex_add {n : ℕ} (i j : RothMvIndex n) (a b : ℕ) :
    rothLastIndex (i + j) (a + b) = rothLastIndex i a + rothLastIndex j b := by
  ext h
  refine Fin.lastCases ?_ (fun t ↦ ?_) h
  · simp [rothLastIndex_last]
  · simp [rothLastIndex_castSucc]

private theorem rothMvWeight_lastIndex {n : ℕ} (r : Fin (n + 1) → ℕ)
    (i : RothMvIndex n) (a : ℕ) :
    rothMvWeight r (rothLastIndex i a) =
      rothMvWeight (fun h ↦ r h.castSucc) i + (a : ℝ) / r (Fin.last n) := by
  unfold rothMvWeight
  rw [Fin.sum_univ_castSucc]
  simp only [rothLastIndex_castSucc, rothLastIndex_last]

private theorem rothLastEquiv_coeff_coeff {n : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin (n + 1)) R) (a : ℕ) (i : RothMvIndex n) :
    ((rothLastEquiv R n P).coeff a).coeff i = P.coeff (rothLastIndex i a) := by
  let d := rothLastIndex i a
  have hmap : Finsupp.mapDomain finSuccEquivLast d = Finsupp.optionElim a i := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain]
    change (Finsupp.equivCongrLeft finSuccEquivLast) d = _
    simpa [d, rothLastIndex, Finsupp.equivCongrLeft_apply] using
      roth_equivMapDomain_symm finSuccEquivLast (Finsupp.optionElim a i)
  unfold rothLastEquiv
  rw [AlgEquiv.trans_apply, MvPolynomial.optionEquivLeft_coeff_coeff]
  rw [← hmap, MvPolynomial.renameEquiv_apply,
    MvPolynomial.coeff_rename_mapDomain finSuccEquivLast finSuccEquivLast.injective]

private theorem rothLastEquiv_natDegree_le {n : ℕ} {R : Type*} [CommSemiring R]
    {P : MvPolynomial (Fin (n + 1)) R} {r : Fin (n + 1) → ℕ}
    (hP : rothDegreeBoundOver P r) :
    (rothLastEquiv R n P).natDegree ≤ r (Fin.last n) := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr hne
  have hcoeff : P.coeff (rothLastIndex i a) ≠ 0 := by
    rw [← rothLastEquiv_coeff_coeff]
    exact MvPolynomial.mem_support_iff.mp hi
  have hmem : rothLastIndex i a ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
  have := hP (rothLastIndex i a) hmem (Fin.last n)
  rw [rothLastIndex_last] at this
  omega

private theorem rothLastEquiv_coeff_degreeBound {n : ℕ} {R : Type*}
    [CommSemiring R] {P : MvPolynomial (Fin (n + 1)) R}
    {r : Fin (n + 1) → ℕ} (hP : rothDegreeBoundOver P r) (a : ℕ) :
    rothDegreeBoundOver ((rothLastEquiv R n P).coeff a)
      (fun h ↦ r h.castSucc) := by
  intro i hi h
  have hcoeff : P.coeff (rothLastIndex i a) ≠ 0 := by
    rw [← rothLastEquiv_coeff_coeff]
    exact MvPolynomial.mem_support_iff.mp hi
  simpa [rothLastIndex_castSucc] using
    hP (rothLastIndex i a) (MvPolynomial.mem_support_iff.mpr hcoeff) h.castSucc

private theorem rothLastEquiv_map {n : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (P : MvPolynomial (Fin (n + 1)) R) :
    rothLastEquiv S n (MvPolynomial.map f P) =
      Polynomial.map (MvPolynomial.map f) (rothLastEquiv R n P) := by
  ext a i
  rw [rothLastEquiv_coeff_coeff, MvPolynomial.coeff_map, Polynomial.coeff_map,
    MvPolynomial.coeff_map, rothLastEquiv_coeff_coeff]

private theorem rothMvL1_lastEquiv_coeff_le {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (a : ℕ) :
    rothMvL1 ((rothLastEquiv ℤ n P).coeff a) ≤ rothMvL1 P := by
  classical
  let Q := (rothLastEquiv ℤ n P).coeff a
  let f : RothMvIndex n → RothMvIndex (n + 1) := fun i ↦ rothLastIndex i a
  have hf : Function.Injective f := rothLastIndex_left_injective a
  have hsubset : Q.support.image f ⊆ P.support := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    apply MvPolynomial.mem_support_iff.mpr
    rw [← rothLastEquiv_coeff_coeff]
    exact MvPolynomial.mem_support_iff.mp hi
  rw [rothMvL1_eq_sum, rothMvL1_eq_sum]
  calc
    ∑ i ∈ Q.support, (Q.coeff i).natAbs =
        ∑ d ∈ Q.support.image f, (P.coeff d).natAbs := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i _hi
        rw [rothLastEquiv_coeff_coeff]
      · exact fun _i _hi _j _hj hij ↦ hf hij
    _ ≤ ∑ d ∈ P.support, (P.coeff d).natAbs :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ Nat.zero_le _)

private theorem rothLastEquiv_eval {n : ℕ} {R : Type*} [CommSemiring R]
    (x : Fin n → R) (y : R) (P : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval (Fin.lastCases y x) P =
      Polynomial.eval y
        (Polynomial.map (MvPolynomial.eval x) (rothLastEquiv R n P)) := by
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

noncomputable def rothLastSlice {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : RothMvIndex n) : ℤ[X] :=
  ∑ a ∈ (rothLastEquiv ℤ n P).support,
    Polynomial.monomial a (((rothLastEquiv ℤ n P).coeff a).coeff i)

private theorem rothLastSlice_coeff {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : RothMvIndex n) (a : ℕ) :
    (rothLastSlice P i).coeff a = P.coeff (rothLastIndex i a) := by
  classical
  rw [rothLastSlice, Polynomial.finsetSum_coeff]
  by_cases ha : a ∈ (rothLastEquiv ℤ n P).support
  · rw [Finset.sum_eq_single a]
    · simp [rothLastEquiv_coeff_coeff]
    · intro b hb hba
      simp [Polynomial.coeff_monomial, hba]
    · exact fun hnot ↦ (hnot ha).elim
  · rw [Finset.sum_eq_zero]
    · rw [← rothLastEquiv_coeff_coeff]
      simpa using (congrArg (fun Q : MvPolynomial (Fin n) ℤ ↦ Q.coeff i)
        (Polynomial.notMem_support_iff.mp ha)).symm
    · intro b hb
      have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
      simp [Polynomial.coeff_monomial, hba]

private theorem rothLastSlice_map_eq_C_mul_of_factorization {n : ℕ}
    (U : MvPolynomial (Fin (n + 1)) ℤ) (V : MvPolynomial (Fin n) ℤ)
    (W : ℚ[X]) (i : RothMvIndex n)
    (hfactor :
      rothLastEquiv ℚ n (MvPolynomial.map (algebraMap ℤ ℚ) U) =
        Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) V) *
          Polynomial.map MvPolynomial.C W) :
    Polynomial.map (algebraMap ℤ ℚ) (rothLastSlice U i) =
      Polynomial.C (V.coeff i : ℚ) * W := by
  ext a
  have hcoeff := congrArg
    (fun Q : Polynomial (MvPolynomial (Fin n) ℚ) ↦ (Q.coeff a).coeff i) hfactor
  rw [Polynomial.coeff_map, rothLastSlice_coeff]
  rw [rothLastEquiv_coeff_coeff, MvPolynomial.coeff_map] at hcoeff
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map] at hcoeff
  rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hcoeff
  simpa [mul_comm] using hcoeff

private theorem rothLastEquiv_hasse_coeff {n : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin (n + 1)) R) (i : RothMvIndex n) (a b : ℕ) :
    (rothLastEquiv R n (rothMvHasse (rothLastIndex i a) P)).coeff b =
      rothMvHasse i ((Polynomial.hasseDeriv a (rothLastEquiv R n P)).coeff b) := by
  ext j
  rw [rothLastEquiv_coeff_coeff, rothMvHasse_coeff, rothMvHasse_coeff,
    Polynomial.hasseDeriv_coeff, ← MvPolynomial.C_eq_coe_nat,
    MvPolynomial.coeff_C_mul, rothLastEquiv_coeff_coeff]
  rw [Fin.prod_univ_castSucc]
  simp only [rothLastIndex_add, rothLastIndex_castSucc, rothLastIndex_last,
    Finsupp.add_apply]
  ring

private theorem rothLastEquiv_hasse_of_tensor_decomposition {n k : ℕ}
    (Q : Polynomial (MvPolynomial (Fin n) ℚ))
    (phi : Fin k → MvPolynomial (Fin n) ℚ) (psi : Fin k → ℚ[X])
    (hQ : Q = ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j))
    (i : RothMvIndex n) (a : ℕ) :
    rothLastEquiv ℚ n
        (rothMvHasse (rothLastIndex i a) ((rothLastEquiv ℚ n).symm Q)) =
      ∑ j, Polynomial.C (rothMvHasse i (phi j)) *
        Polynomial.map MvPolynomial.C (Polynomial.hasseDeriv a (psi j)) := by
  ext b l
  rw [rothLastEquiv_hasse_coeff, AlgEquiv.apply_symm_apply,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.hasseDeriv_coeff]
  rw [hQ, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  rw [← MvPolynomial.C_eq_coe_nat, ← MvPolynomial.smul_eq_C_mul,
    rothMvHasse_smul, rothMvHasse_finset_sum, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_sum]
  rw [Finset.smul_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show phi j * MvPolynomial.C ((psi j).coeff (b + a)) =
      (psi j).coeff (b + a) • phi j by
        rw [MvPolynomial.smul_eq_C_mul]
        ring,
    rothMvHasse_smul, MvPolynomial.coeff_smul]
  simp only [smul_eq_mul]
  rw [mul_comm (rothMvHasse i (phi j)), MvPolynomial.coeff_C_mul,
    Polynomial.hasseDeriv_coeff]
  ring

private theorem roth_exists_tensor_decomposition {n : ℕ}
    (Q : Polynomial (MvPolynomial (Fin n) ℚ)) (hQ : Q ≠ 0) :
    ∃ (k : ℕ) (phi : Fin k → MvPolynomial (Fin n) ℚ) (psi : Fin k → ℚ[X]),
      0 < k ∧ k ≤ Q.natDegree + 1 ∧
        (∀ j, ∃ a ∈ Q.support, phi j = Q.coeff a) ∧
        (∀ j, (psi j).natDegree ≤ Q.natDegree) ∧
        LinearIndependent ℚ phi ∧ LinearIndependent ℚ psi ∧
        Q = ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j) := by
  classical
  let S : Set (MvPolynomial (Fin n) ℚ) :=
    Set.range fun a : Q.support ↦ Q.coeff a
  let _ : Module.Finite ℚ (Submodule.span ℚ S) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  let k := Module.finrank ℚ (Submodule.span ℚ S)
  have hspanNontrivial : Nontrivial (Submodule.span ℚ S) := by
    obtain ⟨b, hb⟩ := Polynomial.support_nonempty.mpr hQ
    have hbne : Q.coeff b ≠ 0 := Polynomial.mem_support_iff.mp hb
    have hbmem : Q.coeff b ∈ Submodule.span ℚ S :=
      Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
    rw [nontrivial_iff]
    refine ⟨⟨Q.coeff b, hbmem⟩, 0, ?_⟩
    intro heq
    apply hbne
    exact congrArg Subtype.val heq
  have hkPos : 0 < k := Module.finrank_pos_iff.mpr hspanNontrivial
  obtain ⟨phi, hphiS, hphiSpan, hphi⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ S
  have hcoeffSpan : ∀ a : ℕ, Q.coeff a ∈ Submodule.span ℚ (Set.range phi) := by
    intro a
    rw [hphiSpan]
    by_cases ha : a ∈ Q.support
    · exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
    · rw [Polynomial.notMem_support_iff.mp ha]
      exact Submodule.zero_mem _
  have hcoordExists : ∀ a : ℕ, ∃ c : Fin k → ℚ,
      ∑ j, c j • phi j = Q.coeff a := by
    intro a
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hcoeffSpan a)
  choose c hc using hcoordExists
  let psi : Fin k → ℚ[X] := fun j ↦
    ∑ a ∈ Q.support, Polynomial.monomial a (c a j)
  have hcZero {a : ℕ} (ha : a ∉ Q.support) : ∀ j, c a j = 0 := by
    have hsum : ∑ j, c a j • phi j = 0 := by
      rw [hc a, Polynomial.notMem_support_iff.mp ha]
    exact Fintype.linearIndependent_iff.mp hphi (c a) hsum
  have hpsiCoeff : ∀ (j : Fin k) (a : ℕ), (psi j).coeff a = c a j := by
    intro j a
    dsimp [psi]
    rw [Polynomial.finsetSum_coeff]
    by_cases ha : a ∈ Q.support
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b hb hba
        simp [Polynomial.coeff_monomial, hba]
      · exact fun hnot ↦ (hnot ha).elim
    · rw [Finset.sum_eq_zero]
      · exact (hcZero ha j).symm
      · intro b hb
        have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
        simp [Polynomial.coeff_monomial, hba]
  choose a ha using hphiS
  have haCoeff : ∀ j, phi j = Q.coeff (a j) := fun j ↦ (ha j).symm
  have haInjective : Function.Injective a := by
    intro i j hij
    apply hphi.injective
    rw [haCoeff i, haCoeff j, hij]
  have hkSupport : k ≤ Q.support.card := by
    simpa using Fintype.card_le_of_injective a haInjective
  have hsupportDegree : Q.support.card ≤ Q.natDegree + 1 := by
    simpa using Finset.card_le_card Polynomial.supp_subset_range_natDegree_succ
  have hkDegree : k ≤ Q.natDegree + 1 := hkSupport.trans hsupportDegree
  have hcSelected : ∀ (j t : Fin k), c (a j) t = if t = j then 1 else 0 := by
    intro j
    let e : Fin k → ℚ := fun t ↦ if t = j then 1 else 0
    have heSum : ∑ t, e t • phi t = phi j := by
      simp [e]
    have hdiff : ∑ t, (c (a j) t - e t) • phi t = 0 := by
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib]
      rw [hc (a j), ← haCoeff j, heSum, sub_self]
    have hz := Fintype.linearIndependent_iff.mp hphi
      (fun t ↦ c (a j) t - e t) hdiff
    intro t
    exact sub_eq_zero.mp (hz t)
  have hpsi : LinearIndependent ℚ psi := by
    rw [Fintype.linearIndependent_iff]
    intro d hd j
    have hcoeff := congrArg (fun P : ℚ[X] ↦ P.coeff (a j)) hd
    have hcoeff' : ∑ t, d t * (psi t).coeff (a j) = 0 := by
      simpa using hcoeff
    have hcoeff'' : ∑ t, d t * c (a j) t = 0 := by
      calc
        ∑ t, d t * c (a j) t = ∑ t, d t * (psi t).coeff (a j) := by
          apply Finset.sum_congr rfl
          intro t _ht
          rw [hpsiCoeff]
        _ = 0 := hcoeff'
    simpa [hcSelected j] using hcoeff''
  have hpsiDegree : ∀ j, (psi j).natDegree ≤ Q.natDegree := by
    intro j
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro b hb
    rw [hpsiCoeff]
    apply hcZero
    intro hmem
    exact (not_le_of_gt hb) (Polynomial.le_natDegree_of_mem_supp b hmem)
  have hdecomp : Q =
      ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j) := by
    apply Polynomial.ext
    intro b
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, hpsiCoeff]
    simpa [Algebra.smul_def, mul_comm] using (hc b).symm
  exact ⟨k, phi, psi, hkPos, hkDegree,
    fun j ↦ ⟨a j, (a j).property, haCoeff j⟩, hpsiDegree, hphi, hpsi, hdecomp⟩

private theorem rothHasseDet_lastEquiv_factorization {n k : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℚ)
    (phi : Fin k → MvPolynomial (Fin n) ℚ) (psi : Fin k → ℚ[X])
    (hP : rothLastEquiv ℚ n P =
      ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j))
    (i : Fin k → RothMvIndex n) :
    rothLastEquiv ℚ n
        (rothHasseDet P
          (fun s ↦ rothLastIndex (i s) 0)
          (fun t ↦ rothLastIndex 0 t.val)) =
      Polynomial.C (Matrix.det fun s j ↦ rothMvHasse (i s) (phi j)) *
        Polynomial.map MvPolynomial.C
          (Matrix.det fun t j ↦ Polynomial.hasseDeriv t.val (psi j)) := by
  classical
  let V : Matrix (Fin k) (Fin k) (MvPolynomial (Fin n) ℚ) :=
    fun s j ↦ rothMvHasse (i s) (phi j)
  let H : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun t j ↦ Polynomial.hasseDeriv t.val (psi j)
  let B : Matrix (Fin k) (Fin k) (MvPolynomial (Fin (n + 1)) ℚ) :=
    fun s t ↦ rothMvHasse
      (rothLastIndex (i s) 0 + rothLastIndex 0 t.val) P
  let A : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun s t ↦ rothLastEquiv ℚ n
      (rothMvHasse (rothLastIndex (i s) t.val) P)
  let VC : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun s j ↦ Polynomial.C (V s j)
  let HC : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun j t ↦ Polynomial.map MvPolynomial.C (H t j)
  have hA : A = VC * HC := by
    funext s t
    rw [Matrix.mul_apply]
    dsimp [A, VC, HC, V, H]
    simpa using rothLastEquiv_hasse_of_tensor_decomposition
      (rothLastEquiv ℚ n P) phi psi hP (i s) t.val
  have hleft : rothLastEquiv ℚ n
        (rothHasseDet P
          (fun s ↦ rothLastIndex (i s) 0)
          (fun t ↦ rothLastIndex 0 t.val)) = A.det := by
    unfold rothHasseDet
    change rothLastEquiv ℚ n B.det = A.det
    calc
      rothLastEquiv ℚ n B.det =
          ((rothLastEquiv ℚ n).toRingHom.mapMatrix B).det :=
        RingHom.map_det (rothLastEquiv ℚ n).toRingHom B
      _ = A.det := by
        congr 1
        funext s t
        change rothLastEquiv ℚ n
            (rothMvHasse (rothLastIndex (i s) 0 + rothLastIndex 0 t.val) P) =
          rothLastEquiv ℚ n (rothMvHasse (rothLastIndex (i s) t.val) P)
        rw [← rothLastIndex_add]
        simp
  rw [hleft, hA, Matrix.det_mul]
  have hVC : VC.det = Polynomial.C V.det := by
    have hmatrix : VC = V.map Polynomial.C := by
      funext s j
      rfl
    rw [hmatrix]
    exact (RingHom.map_det
      (Polynomial.C : MvPolynomial (Fin n) ℚ →+* Polynomial (MvPolynomial (Fin n) ℚ)) V).symm
  have hHC : HC.det = Polynomial.map MvPolynomial.C H.det := by
    let f : ℚ[X] →+* Polynomial (MvPolynomial (Fin n) ℚ) :=
      Polynomial.mapRingHom MvPolynomial.C
    have hmatrix : HC = f.mapMatrix H.transpose := by
      ext j t
      rfl
    have hmapMatrix : f.mapMatrix H.transpose = H.transpose.map f := by
      rfl
    calc
      HC.det = (f.mapMatrix H.transpose).det := congrArg Matrix.det hmatrix
      _ = (H.transpose.map f).det := congrArg Matrix.det hmapMatrix
      _ = f H.transpose.det := (RingHom.map_det f H.transpose).symm
      _ = f H.det := by rw [Matrix.det_transpose]
      _ = Polynomial.map MvPolynomial.C H.det := rfl
  rw [hVC, hHC]

private theorem rothMvHasse_eval_last_of_factorization {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℚ) (V : MvPolynomial (Fin n) ℚ)
    (W : ℚ[X])
    (hfactor : rothLastEquiv ℚ n P =
      Polynomial.C V * Polynomial.map MvPolynomial.C W)
    (x : Fin n → ℚ) (y : ℚ) (i : RothMvIndex n) (a : ℕ) :
    MvPolynomial.eval (Fin.lastCases y x)
        (rothMvHasse (rothLastIndex i a) P) =
      MvPolynomial.eval x (rothMvHasse i V) *
        (Polynomial.hasseDeriv a W).eval y := by
  let phi : Fin 1 → MvPolynomial (Fin n) ℚ := fun _ ↦ V
  let psi : Fin 1 → ℚ[X] := fun _ ↦ W
  have hdecomp : rothLastEquiv ℚ n P =
      ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j) := by
    rw [hfactor]
    simp [phi, psi]
  have hhasse := rothLastEquiv_hasse_of_tensor_decomposition
    (rothLastEquiv ℚ n P) phi psi hdecomp i a
  have hhasse' :
      rothLastEquiv ℚ n (rothMvHasse (rothLastIndex i a) P) =
        Polynomial.C (rothMvHasse i V) *
          Polynomial.map MvPolynomial.C (Polynomial.hasseDeriv a W) := by
    simpa [phi, psi] using hhasse
  have hcomp : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℚ := by
    ext z
    simp
  rw [rothLastEquiv_eval, hhasse', Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.eval_mul,
    Polynomial.eval_C]

private theorem rothLastSlice_hasse_eval {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : RothMvIndex n)
    (a : ℕ) (y : ℚ) :
    MvPolynomial.eval (Fin.lastCases y (fun _ ↦ 0))
        (rothMvHasse (rothLastIndex i a)
          (MvPolynomial.map (algebraMap ℤ ℚ) P)) =
      (Polynomial.hasseDeriv a
        (Polynomial.map (algebraMap ℤ ℚ) (rothLastSlice P i))).eval y := by
  rw [rothLastEquiv_eval]
  congr 1
  apply Polynomial.ext
  intro b
  rw [Polynomial.coeff_map, rothLastEquiv_hasse_coeff]
  change MvPolynomial.eval (0 : Fin n → ℚ) _ = _
  rw [rothMvHasse_eval_zero]
  simp only [Polynomial.hasseDeriv_coeff, Polynomial.coeff_map]
  rw [rothLastSlice_coeff]
  rw [← MvPolynomial.C_eq_coe_nat, ← MvPolynomial.smul_eq_C_mul,
    MvPolynomial.coeff_smul]
  rw [rothLastEquiv_coeff_coeff, MvPolynomial.coeff_map]
  simp [smul_eq_mul]

private theorem rothMvL1_hasse_le {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (i : RothMvIndex m) (r : Fin m → ℕ) (hdeg : rothDegreeBound P r) :
    rothMvL1 (rothMvHasse i P) ≤ 2 ^ (∑ h, r h) * rothMvL1 P := by
  classical
  unfold rothMvHasse
  rw [Finsupp.sum]
  calc
    rothMvL1 (∑ j ∈ P.support,
        MvPolynomial.monomial (j - i)
          ((∏ h, (Nat.choose (j h) (i h) : ℤ)) * P.coeff j))
        ≤ ∑ j ∈ P.support, rothMvL1
          (MvPolynomial.monomial (j - i)
            ((∏ h, (Nat.choose (j h) (i h) : ℤ)) * P.coeff j)) :=
      rothMvL1_finset_sum P.support _
    _ = ∑ j ∈ P.support, (∏ h, Nat.choose (j h) (i h)) * (P.coeff j).natAbs := by
      congr with j
      rw [rothMvL1_monomial, Int.natAbs_mul, ← Nat.cast_prod, Int.natAbs_natCast]
    _ ≤ ∑ j ∈ P.support, 2 ^ (∑ h, r h) * (P.coeff j).natAbs := by
      gcongr with j hj
      calc
        ∏ h, Nat.choose (j h) (i h) ≤ ∏ h, 2 ^ j h := by
          gcongr with h
          exact Nat.choose_le_two_pow (j h) (i h)
        _ ≤ ∏ h, 2 ^ r h := by
          gcongr with h
          exact hdeg j hj h
        _ = 2 ^ (∑ h, r h) := Finset.prod_pow_eq_pow_sum Finset.univ r 2
    _ = 2 ^ (∑ h, r h) * rothMvL1 P := by
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, Finset.mul_sum]

private theorem rothHasseDet_l1_le {m k : ℕ}
    (P : MvPolynomial (Fin m) ℤ) (r : Fin m → ℕ)
    (hP : rothDegreeBound P r) (u v : Fin k → RothMvIndex m) :
    rothMvL1 (rothHasseDet P u v) ≤
      k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ k := by
  apply rothMvL1_det_le
  intro s t
  exact rothMvL1_hasse_le P (u s + v t) r hP

structure RothDeterminantData {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (r : Fin (n + 1) → ℕ) where
  k : ℕ
  k_pos : 0 < k
  k_le : k ≤ r (Fin.last n) + 1
  row : Fin k → RothMvIndex n
  row_order : ∀ s, rothMvOrder (row s) ≤ s
  V : MvPolynomial (Fin n) ℤ
  W : ℚ[X]
  U : MvPolynomial (Fin (n + 1)) ℤ
  V_ne : V ≠ 0
  W_ne : W ≠ 0
  U_def : U = rothHasseDet P
    (fun s ↦ rothLastIndex (row s) 0)
    (fun t ↦ rothLastIndex 0 t.val)
  factorization :
    rothLastEquiv ℚ n (MvPolynomial.map (algebraMap ℤ ℚ) U) =
      Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) V) *
        Polynomial.map MvPolynomial.C W
  V_degree : rothDegreeBound V (fun h ↦ k * r h.castSucc)
  U_degree : rothDegreeBound U (fun h ↦ k * r h)
  V_l1 : rothMvL1 V ≤
    k.factorial * (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ k
  U_l1 : rothMvL1 U ≤
    k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ k

private theorem roth_exists_determinant_data {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (r : Fin (n + 1) → ℕ)
    (hPne : P ≠ 0) (hPdeg : rothDegreeBound P r) :
    Nonempty (RothDeterminantData P r) := by
  classical
  let castQ : ℤ →+* ℚ := algebraMap ℤ ℚ
  let PQ := MvPolynomial.map castQ P
  let Q := rothLastEquiv ℚ n PQ
  have hPQne : PQ ≠ 0 := by
    simpa [PQ] using (MvPolynomial.map_injective castQ Int.cast_injective).ne hPne
  have hQne : Q ≠ 0 := (rothLastEquiv ℚ n).injective.ne hPQne
  obtain ⟨k, phi, psi, hk, hkQ, hphi, hpsiDeg, hphiLI, hpsiLI, hdecomp⟩ :=
    roth_exists_tensor_decomposition Q hQne
  have hPQdeg : rothDegreeBoundOver PQ r :=
    rothDegreeBoundOver_map castQ hPdeg
  have hQdeg : Q.natDegree ≤ r (Fin.last n) :=
    rothLastEquiv_natDegree_le hPQdeg
  have hkR : k ≤ r (Fin.last n) + 1 := hkQ.trans (Nat.add_le_add_right hQdeg 1)
  choose a haQ hphiCoeff using hphi
  let phiZ : Fin k → MvPolynomial (Fin n) ℤ :=
    fun j ↦ (rothLastEquiv ℤ n P).coeff (a j)
  have hphiMap : ∀ j, MvPolynomial.map castQ (phiZ j) = phi j := by
    intro j
    have hmap := congrArg (fun F : Polynomial (MvPolynomial (Fin n) ℚ) ↦
      F.coeff (a j)) (rothLastEquiv_map castQ P)
    rw [Polynomial.coeff_map] at hmap
    exact hmap.symm.trans (hphiCoeff j).symm
  have hphiZdeg : ∀ j, rothDegreeBound (phiZ j) (fun h ↦ r h.castSucc) := by
    intro j
    exact rothLastEquiv_coeff_degreeBound hPdeg (a j)
  have hphiDeg : ∀ j, rothDegreeBoundOver (phi j) (fun h ↦ r h.castSucc) := by
    intro j
    rw [← hphiMap j]
    exact rothDegreeBoundOver_map castQ (hphiZdeg j)
  obtain ⟨row, hrowOrder, hrowDet⟩ :=
    roth_exists_generalized_wronskian phi (fun h ↦ r h.castSucc) hphiLI hphiDeg
  let V : MvPolynomial (Fin n) ℤ :=
    Matrix.det fun s j ↦ rothMvHasse (row s) (phiZ j)
  let W : ℚ[X] := Matrix.det fun t j ↦ Polynomial.hasseDeriv t.val (psi j)
  let U : MvPolynomial (Fin (n + 1)) ℤ := rothHasseDet P
    (fun s ↦ rothLastIndex (row s) 0)
    (fun t ↦ rothLastIndex 0 t.val)
  have hVmap : MvPolynomial.map castQ V =
      Matrix.det fun s j ↦ rothMvHasse (row s) (phi j) := by
    let A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin n) ℤ) :=
      fun s j ↦ rothMvHasse (row s) (phiZ j)
    change MvPolynomial.map castQ A.det = _
    rw [RingHom.map_det]
    congr 1
    funext s j
    change MvPolynomial.map castQ (rothMvHasse (row s) (phiZ j)) = _
    rw [rothMvHasse_map, hphiMap]
  have hVne : V ≠ 0 := by
    intro hzero
    apply hrowDet
    rw [← hVmap, hzero, map_zero]
  have hWne : W ≠ 0 := roth_poly_hasse_wronskian_ne_zero psi hpsiLI
  have hfactor : rothLastEquiv ℚ n (MvPolynomial.map castQ U) =
      Polynomial.C (MvPolynomial.map castQ V) * Polynomial.map MvPolynomial.C W := by
    rw [show MvPolynomial.map castQ U = rothHasseDet PQ
        (fun s ↦ rothLastIndex (row s) 0)
        (fun t ↦ rothLastIndex 0 t.val) by
      dsimp [U, PQ]
      exact rothHasseDet_map castQ P _ _]
    rw [hVmap]
    exact rothHasseDet_lastEquiv_factorization PQ phi psi hdecomp row
  have hVdegree : rothDegreeBound V (fun h ↦ k * r h.castSucc) := by
    dsimp [V]
    apply rothDegreeBound_det
    intro s j
    exact rothDegreeBoundOver_hasse (hphiZdeg j) (row s)
  have hUdegree : rothDegreeBound U (fun h ↦ k * r h) := by
    dsimp [U]
    exact rothHasseDet_degreeBound hPdeg _ _
  have hVl1 : rothMvL1 V ≤
      k.factorial * (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ k := by
    dsimp [V]
    apply rothMvL1_det_le
    intro s j
    calc
      rothMvL1 (rothMvHasse (row s) (phiZ j)) ≤
          2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 (phiZ j) :=
        rothMvL1_hasse_le (phiZ j) (row s) _ (hphiZdeg j)
      _ ≤ 2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P := by
        gcongr
        exact rothMvL1_lastEquiv_coeff_le P (a j)
  have hUl1 : rothMvL1 U ≤
      k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ k := by
    dsimp [U]
    exact rothHasseDet_l1_le P r hPdeg _ _
  exact ⟨{
    k := k
    k_pos := hk
    k_le := hkR
    row := row
    row_order := hrowOrder
    V := V
    W := W
    U := U
    V_ne := hVne
    W_ne := hWne
    U_def := rfl
    factorization := hfactor
    V_degree := hVdegree
    U_degree := hUdegree
    V_l1 := hVl1
    U_l1 := hUl1
  }⟩

def rothPolyL1 (P : ℤ[X]) : ℕ :=
  rothFinsuppL1 P.toFinsupp.coeff

private theorem rothPolyL1_coeff_le (P : ℤ[X]) (n : ℕ) :
    (P.coeff n).natAbs ≤ rothPolyL1 P := by
  exact rothFinsuppL1_apply_le P.toFinsupp.coeff n

private theorem rothPolyL1_eq_sum (P : ℤ[X]) :
    rothPolyL1 P = ∑ n ∈ P.support, (P.coeff n).natAbs := by
  unfold rothPolyL1 rothFinsuppL1
  rw [Polynomial.support_toFinsupp]
  simp only [Polynomial.toFinsupp_apply]

private theorem rothPolyL1_le_natDegree_succ_mul (P : ℤ[X]) (H : ℕ)
    (hcoeff : ∀ n, (P.coeff n).natAbs ≤ H) :
    rothPolyL1 P ≤ (P.natDegree + 1) * H := by
  rw [rothPolyL1_eq_sum]
  calc
    ∑ n ∈ P.support, (P.coeff n).natAbs ≤ ∑ _n ∈ P.support, H := by
      gcongr with n
      exact hcoeff n
    _ = P.support.card * H := by simp
    _ ≤ (P.natDegree + 1) * H := by
      gcongr
      simpa using Finset.card_le_card Polynomial.supp_subset_range_natDegree_succ

private theorem rothLastSlice_natDegree_le {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (hP : rothDegreeBound P r) (i : RothMvIndex n) :
    (rothLastSlice P i).natDegree ≤ r (Fin.last n) := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [rothLastSlice_coeff]
  by_contra hne
  have hmem : rothLastIndex i a ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
  have hle := hP (rothLastIndex i a) hmem (Fin.last n)
  rw [rothLastIndex_last] at hle
  omega

private theorem rothPolyL1_lastSlice_le {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (hP : rothDegreeBound P r) (i : RothMvIndex n) :
    rothPolyL1 (rothLastSlice P i) ≤
      (r (Fin.last n) + 1) * rothMvL1 P := by
  calc
    rothPolyL1 (rothLastSlice P i) ≤
        ((rothLastSlice P i).natDegree + 1) * rothMvL1 P :=
      rothPolyL1_le_natDegree_succ_mul _ _ fun a ↦ by
        rw [rothLastSlice_coeff]
        exact rothMvL1_coeff_le P (rothLastIndex i a)
    _ ≤ (r (Fin.last n) + 1) * rothMvL1 P := by
      gcongr
      exact rothLastSlice_natDegree_le hP i

structure RothIntegralFactorData {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) where
  coeffIndex : RothMvIndex n
  coeff_ne : d.V.coeff coeffIndex ≠ 0
  WZ : ℤ[X]
  WZ_ne : WZ ≠ 0
  WZ_degree : WZ.natDegree ≤ d.k * r (Fin.last n)
  WZ_l1 : rothPolyL1 WZ ≤
    (d.k * r (Fin.last n) + 1) *
      (d.k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k)
  scaled_factorization :
    rothLastEquiv ℚ n
        ((d.V.coeff coeffIndex : ℚ) •
          MvPolynomial.map (algebraMap ℤ ℚ) d.U) =
      Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) d.V) *
        Polynomial.map MvPolynomial.C
          (Polynomial.map (algebraMap ℤ ℚ) WZ)

private theorem roth_exists_integral_factor_data {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) :
    Nonempty (RothIntegralFactorData d) := by
  classical
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr d.V_ne
  have hcoeff : d.V.coeff i ≠ 0 := MvPolynomial.mem_support_iff.mp hi
  let WZ := rothLastSlice d.U i
  have hmapW : Polynomial.map (algebraMap ℤ ℚ) WZ =
      Polynomial.C (d.V.coeff i : ℚ) * d.W := by
    exact rothLastSlice_map_eq_C_mul_of_factorization d.U d.V d.W i d.factorization
  have hcoeffQ : (d.V.coeff i : ℚ) ≠ 0 := by exact_mod_cast hcoeff
  have hWZne : WZ ≠ 0 := by
    intro hzero
    have hright : Polynomial.C (d.V.coeff i : ℚ) * d.W = 0 := by
      rw [← hmapW, hzero, Polynomial.map_zero]
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hcoeffQ) d.W_ne) hright
  have hWZdegree : WZ.natDegree ≤ d.k * r (Fin.last n) := by
    exact rothLastSlice_natDegree_le d.U_degree i
  have hWZl1 : rothPolyL1 WZ ≤
      (d.k * r (Fin.last n) + 1) *
        (d.k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k) := by
    exact (rothPolyL1_lastSlice_le d.U_degree i).trans
      (Nat.mul_le_mul_left _ d.U_l1)
  have hscaled :
      rothLastEquiv ℚ n
          ((d.V.coeff i : ℚ) • MvPolynomial.map (algebraMap ℤ ℚ) d.U) =
        Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) d.V) *
          Polynomial.map MvPolynomial.C
            (Polynomial.map (algebraMap ℤ ℚ) WZ) := by
    rw [map_smul, d.factorization, hmapW, Polynomial.map_mul,
      Polynomial.map_C]
    simp only [Algebra.smul_def]
    rw [show algebraMap ℚ (Polynomial (MvPolynomial (Fin n) ℚ))
      (d.V.coeff i : ℚ) = Polynomial.C (MvPolynomial.C (d.V.coeff i : ℚ)) by simp]
    ring
  exact ⟨{
    coeffIndex := i
    coeff_ne := hcoeff
    WZ := WZ
    WZ_ne := hWZne
    WZ_degree := hWZdegree
    WZ_l1 := hWZl1
    scaled_factorization := hscaled
  }⟩

noncomputable def rothBoxIndex {m : ℕ} {r : Fin m → ℕ}
    (j : RothBox r) : RothMvIndex m :=
  Finsupp.equivFunOnFinite.symm fun h ↦ j h

noncomputable def rothMvOfCoeff {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r) :
    MvPolynomial (Fin m) ℤ :=
  ∑ j, MvPolynomial.monomial (rothBoxIndex j) (c j)

noncomputable def rothPowerCoord (g : ℤ[X]) : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 =>
      Polynomial.X * rothPowerCoord g n -
        Polynomial.C ((rothPowerCoord g n).coeff (g.natDegree - 1)) * g

noncomputable def rothHasseEval {m : ℕ} {R : Type*} [CommRing R]
    {r : Fin m → ℕ} (c : RothCoeff r) (i : RothMultiIndex m) (x : Fin m → R) : R :=
  ∑ j, (c j : R) * ∏ h, (Nat.choose (j h) (i h) : R) * x h ^ (j h - i h)

noncomputable def rothEval {m : ℕ} {R : Type*} [CommRing R]
    {r : Fin m → ℕ} (c : RothCoeff r) (x : Fin m → R) : R :=
  ∑ j, (c j : R) * ∏ h, x h ^ (j h : ℕ)

noncomputable def rothWeight {m : ℕ} (r : Fin m → ℕ)
    (i : RothMultiIndex m) : ℝ :=
  ∑ h, (i h : ℝ) / r h

def rothRidoutBoxComplement {m : ℕ} (r : Fin m → ℕ) (j : RothBox r) :
    RothBox r :=
  fun h ↦ ⟨r h - j h, Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩

noncomputable def rothCentered {m : ℕ} (r : Fin m → ℕ)
    (j : RothBox r) (h : Fin m) : ℝ :=
  (j h : ℝ) / r h - 1 / 2

noncomputable def rothCenteredSum {m : ℕ} (r : Fin m → ℕ)
    (j : RothBox r) : ℝ :=
  ∑ h, rothCentered r j h

def rothFlip {m : ℕ} (r : Fin m → ℕ) (h : Fin m) (j : RothBox r) :
    RothBox r :=
  Function.update j h ⟨r h - j h, Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩

private theorem rothFlip_apply_same {m : ℕ} (r : Fin m → ℕ) (h : Fin m)
    (j : RothBox r) :
    ((rothFlip r h j) h : ℕ) = r h - j h := by
  simp [rothFlip]

private theorem rothFlip_apply_ne {m : ℕ} (r : Fin m → ℕ) {h k : Fin m}
    (hhk : k ≠ h) (j : RothBox r) :
    rothFlip r h j k = j k := by
  simp [rothFlip, hhk]

private theorem rothFlip_involutive {m : ℕ} (r : Fin m → ℕ) (h : Fin m) :
    Function.Involutive (rothFlip r h) := by
  intro j
  funext k
  by_cases hkh : k = h
  · subst k
    apply Fin.ext
    rw [rothFlip_apply_same, rothFlip_apply_same]
    have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
    omega
  · rw [rothFlip_apply_ne r hkh, rothFlip_apply_ne r hkh]

noncomputable def rothFlipEquiv {m : ℕ} (r : Fin m → ℕ) (h : Fin m) :
    RothBox r ≃ RothBox r :=
  (rothFlip_involutive r h).toPerm (rothFlip r h)

noncomputable def rothLowIndices {m : ℕ} (r : Fin m → ℕ) (γ : ℝ) :
    Finset (RothBox r) :=
  Finset.univ.filter fun i ↦
    rothWeight r (fun h ↦ i h) < (m : ℝ) * (1 / 2 - γ)

abbrev RothLowIndex {m : ℕ} (r : Fin m → ℕ) (γ : ℝ) :=
  {i : RothBox r // i ∈ rothLowIndices r γ}

def rothZeroBox {m : ℕ} (r : Fin m → ℕ) : RothBox r :=
  fun h ↦ ⟨0, Nat.succ_pos (r h)⟩

def rothVanishesBelow {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r)
    (x : Fin m → ℝ) (t : ℝ) : Prop :=
  ∀ i, rothWeight r i < t → rothHasseEval c i x = 0

noncomputable def rothDenProduct {m : ℕ} (q : Fin m → ℚ)
    (r : Fin m → ℕ) : ℕ :=
  ∏ h, (q h).den ^ r h

noncomputable def rothClearEval {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (q : Fin m → ℚ) (r : Fin m → ℕ) : ℤ :=
  ∑ d ∈ P.support, P.coeff d *
    ∏ h, (q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)

def rothRidoutExponent {m : ℕ} {ι : Type*} (r : Fin m → ℕ)
    (a b : Fin m → ι → ℕ) (k : RothMvIndex m) (l : ι) : ℕ :=
  ∑ h, (a h l * k h + b h l * (r h - k h))

private theorem roth_finite_rat_of_abs_le_of_den_le (B : ℝ) (N : ℕ) :
    Set.Finite {q : ℚ | |(q : ℝ)| ≤ B ∧ q.den ≤ N} := by
  let K : ℤ := ⌈B * N⌉
  let f : ℚ → ℤ × ℕ := fun q ↦ (q.num, q.den)
  apply Set.Finite.of_finite_image (f := f)
  · refine ((Set.finite_Icc (-K) K).prod (Set.finite_Icc 0 N)).subset ?_
    rintro _ ⟨q, hq, rfl⟩
    have hden0 : (0 : ℝ) ≤ q.den := by positivity
    have hB : 0 ≤ B := (abs_nonneg (q : ℝ)).trans hq.1
    have hnum : |(q.num : ℝ)| ≤ B * N := by
      calc
        |(q.num : ℝ)| = |(q : ℝ)| * q.den := by
          rw [Rat.cast_def, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
          field_simp
        _ ≤ B * N := mul_le_mul hq.1 (by exact_mod_cast hq.2) hden0 hB
    have hnumKReal : |(q.num : ℝ)| ≤ (K : ℝ) :=
      hnum.trans (Int.le_ceil (B * N))
    have hnumK : |q.num| ≤ K := by exact_mod_cast hnumKReal
    change (-K ≤ q.num ∧ q.num ≤ K) ∧ 0 ≤ q.den ∧ q.den ≤ N
    exact ⟨abs_le.mp hnumK, Nat.zero_le _, hq.2⟩
  · intro a _ b _ hab
    change (a.num, a.den) = (b.num, b.den) at hab
    exact Rat.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

private theorem roth_abs_rat_le_of_approx {α p : ℝ} (hp : 0 < p) (q : ℚ)
    (hq : |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p) :
    |(q : ℝ)| ≤ |α| + 1 := by
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have hrpow : 1 ≤ Real.rpow (q.den : ℝ) p := Real.one_le_rpow hden hp.le
  have hrpow0 : 0 < Real.rpow (q.den : ℝ) p := Real.rpow_pos_of_pos (by positivity) _
  have hdist : |α - (q : ℝ)| < 1 := hq.trans_le ((div_le_one₀ hrpow0).2 hrpow)
  calc
    |(q : ℝ)| = |((q : ℝ) - α) + α| := by ring_nf
    _ ≤ |(q : ℝ) - α| + |α| := abs_add_le _ _
    _ ≤ 1 + |α| := by
      rw [abs_sub_comm]
      exact add_le_add hdist.le le_rfl
    _ = |α| + 1 := by ring

private theorem roth_finite_approximants_of_den_le (α p : ℝ) (hp : 0 < p) (N : ℕ) :
    Set.Finite {q : ℚ |
      |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p ∧ q.den ≤ N} := by
  refine (roth_finite_rat_of_abs_le_of_den_le (|α| + 1) N).subset ?_
  rintro q ⟨hq, hden⟩
  exact ⟨roth_abs_rat_le_of_approx hp q hq, hden⟩

private theorem roth_ridout_exists_approx_den_gt {α p : ℝ} (hp : 0 < p)
    (A : Set ℚ)
    (hA : A ⊆ {q : ℚ | |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p})
    (hinf : A.Infinite) (N : ℕ) :
    ∃ q ∈ A, N < q.den := by
  by_contra! hbounded
  apply hinf
  refine (roth_finite_approximants_of_den_le α p hp N).subset ?_
  intro q hq
  exact ⟨hA hq, hbounded q hq⟩

private theorem roth_den_pow_le_natAbs_leadingCoeff_of_pow_dvd
    (P : ℤ[X]) (q : ℚ) (k : ℕ) (hP : P ≠ 0)
    (hdiv : (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num) ^ k ∣ P) :
    q.den ^ k ≤ P.leadingCoeff.natAbs := by
  let L : ℤ[X] := Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num
  have hL : L.leadingCoeff = (q.den : ℤ) := by
    dsimp [L]
    rw [Polynomial.leadingCoeff_sub_of_degree_lt]
    · exact Polynomial.leadingCoeff_C_mul_X _
    · rw [Polynomial.degree_C_mul_X (by exact_mod_cast q.pos.ne')]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  have hdvdZ : ((q.den ^ k : ℕ) : ℤ) ∣ P.leadingCoeff := by
    obtain ⟨Q, hQ⟩ := hdiv
    rw [hQ, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, hL]
    norm_cast
    exact dvd_mul_right _ _
  refine Nat.le_of_dvd
    (Int.natAbs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)) ?_
  simpa using (Int.natAbs_dvd_natAbs.mpr hdvdZ)

private theorem roth_rat_linear_isPrimitive (q : ℚ) :
    (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro a ha
  have hall := (Polynomial.C_dvd_iff_dvd_coeff a _).mp ha
  have hanum : a ∣ q.num := by
    have h := hall 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h
    norm_num at h
    exact h
  have haden : a ∣ (q.den : ℤ) := by
    have h := hall 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h
    norm_num at h
    exact h
  have hanum' : a.natAbs ∣ q.num.natAbs := Int.natAbs_dvd_natAbs.mpr hanum
  have haden' : a.natAbs ∣ q.den := by
    simpa using (Int.natAbs_dvd_natAbs.mpr haden)
  apply Int.isUnit_iff_natAbs_eq.mpr
  exact Nat.dvd_one.mp
    ((Nat.dvd_gcd hanum' haden').trans (by rw [q.reduced.gcd_eq_one]))

private theorem roth_isPrimitive_pow (P : ℤ[X]) (hP : P.IsPrimitive) (k : ℕ) :
    (P ^ k).IsPrimitive := by
  induction k with
  | zero =>
      rw [pow_zero]
      exact Polynomial.isPrimitive_one
  | succ k ih =>
      rw [pow_succ]
      exact ih.mul hP

private theorem roth_rat_linear_pow_dvd_of_map_dvd (P : ℤ[X]) (q : ℚ) (k : ℕ)
    (hdiv : (Polynomial.X - Polynomial.C q) ^ k ∣
      P.map (Int.castRingHom ℚ)) :
    (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num) ^ k ∣ P := by
  let L : ℤ[X] := Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num
  let A : ℚ[X] := Polynomial.X - Polynomial.C q
  have hmapL : L.map (Int.castRingHom ℚ) = Polynomial.C (q.den : ℚ) * A := by
    dsimp [L, A]
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C, mul_sub, ← Polynomial.C_mul, Rat.den_mul_eq_num]
    rfl
  have hunit : IsUnit (Polynomial.C (q.den : ℚ)) :=
    Polynomial.isUnit_C.mpr
      (show IsUnit (q.den : ℚ) from (by exact_mod_cast q.pos.ne' : (q.den : ℚ) ≠ 0).isUnit)
  have hassoc : Associated ((L ^ k).map (Int.castRingHom ℚ)) (A ^ k) := by
    rw [Polynomial.map_pow, hmapL, mul_pow]
    exact associated_unit_mul_left _ _ (hunit.pow k)
  apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
    (L ^ k) P (roth_isPrimitive_pow L (roth_rat_linear_isPrimitive q) k)).mpr
  rwa [Associated.dvd_iff_dvd_left hassoc]

private theorem roth_X_sub_C_pow_dvd_of_hasse_eval_eq_zero (P : ℚ[X]) (q : ℚ) (k : ℕ)
    (hzero : ∀ n < k, (Polynomial.hasseDeriv n P).eval q = 0) :
    (Polynomial.X - Polynomial.C q) ^ k ∣ P := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, ← Polynomial.taylor_apply,
    Polynomial.X_pow_dvd_iff]
  intro n hn
  rw [Polynomial.taylor_coeff]
  exact hzero n hn

private theorem roth_univariate_index_le (P : ℤ[X]) (q : ℚ) (k r : ℕ) (δ : ℝ)
    (hP : P ≠ 0) (hq : 2 ≤ q.den) (hr : 0 < r)
    (hdiv : (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num) ^ k ∣ P)
    (hheight : (P.leadingCoeff.natAbs : ℝ) ≤
      Real.rpow (q.den : ℝ) (δ * r)) :
    (k : ℝ) / r ≤ δ := by
  have hpowNat := roth_den_pow_le_natAbs_leadingCoeff_of_pow_dvd P q k hP hdiv
  have hpow : Real.rpow (q.den : ℝ) k ≤ Real.rpow (q.den : ℝ) (δ * r) := by
    calc
      Real.rpow (q.den : ℝ) k = ((q.den ^ k : ℕ) : ℝ) := by
        rw [Real.rpow_eq_pow, Real.rpow_natCast]
        norm_cast
      _ ≤ (P.leadingCoeff.natAbs : ℝ) := by exact_mod_cast hpowNat
      _ ≤ Real.rpow (q.den : ℝ) (δ * r) := hheight
  have hk : (k : ℝ) ≤ δ * r :=
    (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast hq)).le_iff_le.mp hpow
  exact (div_le_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2 (by simpa [mul_comm] using hk)

private theorem roth_triangular_sum_lower {θ δ : ℝ} {r k : ℕ}
    (hθ : 0 < θ) (hθone : θ ≤ 1) (hδ : δ ≤ θ / 4)
    (hr : 0 < r) (hrlarge : 16 ≤ θ * r)
    (hk : 0 < k) (hkr : k ≤ r + 1) :
    θ ^ 2 / 64 ≤
      (∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r)) / k := by
  let N : ℕ := ⌊θ * r / 8⌋₊
  have hxnonneg : 0 ≤ θ * (r : ℝ) / 8 := by positivity
  have hxlarge : 2 ≤ θ * (r : ℝ) / 8 := by linarith
  have hNle : (N : ℝ) ≤ θ * r / 8 := by
    exact Nat.floor_le hxnonneg
  have hxlt : θ * r / 8 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hNlower : θ * (r : ℝ) / 16 ≤ N := by linarith
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNlower
    exact_mod_cast this
  have hterm : ∀ t : Fin k, t.val < N →
      θ / 2 ≤ max 0 (θ - δ - (t : ℝ) / r) := by
    intro t ht
    have htN : (t.val : ℝ) < N := by exact_mod_cast ht
    have htx : (t.val : ℝ) < θ * r / 8 := htN.trans_le hNle
    have htdiv : (t.val : ℝ) / r < θ / 8 := by
      apply (div_lt_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2
      nlinarith
    exact (by linarith : θ / 2 ≤ θ - δ - (t : ℝ) / r).trans
      (le_max_right _ _)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply (le_div_iff₀ hkR).2
  by_cases hkN : k ≤ N
  · have hsum : (k : ℝ) * (θ / 2) ≤
        ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) := by
      calc
        (k : ℝ) * (θ / 2) = ∑ _t : Fin k, θ / 2 := by simp
        _ ≤ ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) := by
          gcongr with t
          exact hterm t (lt_of_lt_of_le t.isLt hkN)
    calc
      θ ^ 2 / 64 * k ≤ (k : ℝ) * (θ / 2) := by
        have : θ ^ 2 / 64 ≤ θ / 2 := by nlinarith [sq_nonneg θ]
        nlinarith
      _ ≤ _ := hsum
  · have hNk : N ≤ k := (Nat.le_of_lt (lt_of_not_ge hkN))
    let S : Finset (Fin k) := Finset.univ.filter fun t ↦ t.val < N
    have hcardS : S.card = N := by
      rw [← Fintype.card_coe]
      let e : S ≃ Fin N :=
        { toFun := fun t ↦ ⟨t.val.val, by
              have := t.property
              change t.val ∈ Finset.univ.filter (fun u : Fin k ↦ u.val < N) at this
              exact (Finset.mem_filter.mp this).2⟩
          invFun := fun t ↦ ⟨⟨t.val, t.isLt.trans_le hNk⟩, by
              simp [S]⟩
          left_inv := by intro t; ext; rfl
          right_inv := by intro t; ext; rfl }
      exact (Fintype.card_congr e).trans (Fintype.card_fin N)
    have hsumS : (N : ℝ) * (θ / 2) ≤
        ∑ t ∈ S, max 0 (θ - δ - (t : ℝ) / r) := by
      calc
        (N : ℝ) * (θ / 2) = ∑ _t ∈ S, θ / 2 := by simp [hcardS]
        _ ≤ ∑ t ∈ S, max 0 (θ - δ - (t : ℝ) / r) := by
          gcongr with t ht
          exact hterm t (by simpa [S] using ht)
    have hsumAll : (N : ℝ) * (θ / 2) ≤
        ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) := by
      exact hsumS.trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ le_max_left _ _))
    have hkrR : (k : ℝ) ≤ 2 * r := by
      exact_mod_cast (hkr.trans (by omega : r + 1 ≤ 2 * r))
    calc
      θ ^ 2 / 64 * k ≤ θ ^ 2 * r / 32 := by
        nlinarith [sq_nonneg θ]
      _ ≤ (N : ℝ) * (θ / 2) := by
        nlinarith
      _ ≤ _ := hsumAll

noncomputable def rothIntPolynomial (α : ℝ) : ℤ[X] :=
  IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α)

noncomputable def rothIntegralPolynomial (α : ℝ) : ℤ[X] :=
  (rothIntPolynomial α).integralNormalization

noncomputable def rothCoordinateBase (α : ℝ) : ℕ :=
  max (rothIntPolynomial α).leadingCoeff.natAbs
    (rothPolyL1 (rothIntegralPolynomial α) + 1)

noncomputable def rothScaledPowerCoord (α : ℝ) (S n : ℕ) : ℤ[X] :=
  Polynomial.C ((rothIntPolynomial α).leadingCoeff ^ (S - n)) *
    rothPowerCoord (rothIntegralPolynomial α) n

noncomputable def rothTermDegree {m : ℕ} {r : Fin m → ℕ}
    (i j : RothBox r) : ℕ :=
  ∑ h, ((j h : ℕ) - (i h : ℕ))

noncomputable def rothAuxTerm (α : ℝ) {m : ℕ} {r : Fin m → ℕ}
    (i j : RothBox r) : ℤ[X] :=
  Polynomial.C (∏ h, (Nat.choose (j h) (i h) : ℤ)) *
    rothScaledPowerCoord α (∑ h, r h) (rothTermDegree i j)

noncomputable def rothAuxMatrix (α : ℝ) {m : ℕ} (r : Fin m → ℕ) (γ : ℝ) :
    Matrix (RothLowIndex r γ × Fin (rothIntegralPolynomial α).natDegree)
      (RothBox r) ℤ :=
  fun u j ↦ (rothAuxTerm α u.1.1 j).coeff u.2

noncomputable def rothRidoutAuxMatrix (α : ℝ) {m : ℕ}
    (r : Fin m → ℕ) (γ : ℝ) :
    Matrix (RothLowIndex r γ × Fin ((rothIntegralPolynomial α).natDegree + 2))
      (RothBox r) ℤ :=
  fun u j ↦
    Fin.lastCases
      (if j = rothRidoutBoxComplement r u.1.1 then 1 else 0)
      (fun v ↦ Fin.lastCases
        (if j = u.1.1 then 1 else 0)
        (fun k ↦ rothAuxMatrix α r γ (u.1, k) j) v) u.2

noncomputable def rothAuxCombination (α : ℝ) {m : ℕ} {r : Fin m → ℕ}
    (i : RothBox r) (c : RothCoeff r) : ℤ[X] :=
  ∑ j, Polynomial.C (c j) * rothAuxTerm α i j

private theorem roth_succ_le_two_pow {n : ℕ} (hn : 0 < n) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · calc
          n + 1 + 1 ≤ 2 * (n + 1) := by omega
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (ih (Nat.pos_of_ne_zero hn0))
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

private theorem roth_exists_rpow_threshold {lam : ℝ} (hlam : 0 < lam) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q : ℕ, Q ≤ q →
      (2 : ℝ) ≤ Real.rpow q lam := by
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ lam :=
    Filter.tendsto_atTop.1 (tendsto_rpow_atTop hlam) 2
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨N, hN⟩ := exists_nat_ge A
  refine ⟨max 2 N, le_max_left _ _, fun q hq ↦ ?_⟩
  apply hA q
  exact hN.trans (by exact_mod_cast (le_trans (le_max_right 2 N) hq))

private theorem roth_factorial_le_two_pow_sq {k : ℕ} (hk : 0 < k) :
    k.factorial ≤ 2 ^ (k * k) := by
  have hktwo : k ≤ 2 ^ k :=
    (Nat.le_add_right k 1).trans (roth_succ_le_two_pow hk)
  calc
    k.factorial ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := by gcongr
    _ = 2 ^ (k * k) := by rw [pow_mul]

private theorem roth_determinant_V_l1_coarse {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) :
    rothMvL1 d.V ≤
      2 ^ (d.k * d.k + d.k * (∑ h : Fin n, r h.castSucc)) *
        rothMvL1 P ^ d.k := by
  calc
    rothMvL1 d.V ≤
        d.k.factorial *
          (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ d.k := d.V_l1
    _ ≤ 2 ^ (d.k * d.k) *
          (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ d.k := by
      gcongr
      exact roth_factorial_le_two_pow_sq d.k_pos
    _ = 2 ^ (d.k * d.k + d.k * (∑ h : Fin n, r h.castSucc)) *
          rothMvL1 P ^ d.k := by
      rw [mul_pow, ← pow_mul]
      rw [show 2 ^ (d.k * d.k) *
          (2 ^ ((∑ h : Fin n, r h.castSucc) * d.k) * rothMvL1 P ^ d.k) =
          (2 ^ (d.k * d.k) *
            2 ^ ((∑ h : Fin n, r h.castSucc) * d.k)) * rothMvL1 P ^ d.k by ring,
        ← pow_add]
      congr 2
      ring

private theorem roth_determinant_W_l1_coarse {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) (e : RothIntegralFactorData d)
    (hrlast : 0 < r (Fin.last n)) :
    rothPolyL1 e.WZ ≤
      2 ^ (d.k * r (Fin.last n) + d.k * d.k + d.k * (∑ h, r h)) *
        rothMvL1 P ^ d.k := by
  have hkr : 0 < d.k * r (Fin.last n) := Nat.mul_pos d.k_pos hrlast
  calc
    rothPolyL1 e.WZ ≤
        (d.k * r (Fin.last n) + 1) *
          (d.k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k) := e.WZ_l1
    _ ≤ 2 ^ (d.k * r (Fin.last n)) *
          (2 ^ (d.k * d.k) *
            (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k) := by
      gcongr
      · exact roth_succ_le_two_pow hkr
      · exact roth_factorial_le_two_pow_sq d.k_pos
    _ = 2 ^ (d.k * r (Fin.last n) + d.k * d.k + d.k * (∑ h, r h)) *
          rothMvL1 P ^ d.k := by
      rw [mul_pow, ← pow_mul]
      rw [show 2 ^ (d.k * r (Fin.last n)) *
          (2 ^ (d.k * d.k) * (2 ^ ((∑ h, r h) * d.k) * rothMvL1 P ^ d.k)) =
          (2 ^ (d.k * r (Fin.last n)) * 2 ^ (d.k * d.k) *
            2 ^ ((∑ h, r h) * d.k)) * rothMvL1 P ^ d.k by ring,
        ← pow_add, ← pow_add]
      congr 2
      ring

private theorem roth_absorb_height (q H C k r A : ℕ) (δ lam : ℝ)
    (hq : 2 ≤ q) (hlam : 0 ≤ lam)
    (hbase : (2 : ℝ) ≤ Real.rpow q lam)
    (hH : (H : ℝ) ≤ Real.rpow q (δ * r))
    (hC : C ≤ A * k * r) :
    ((2 ^ C * H ^ k : ℕ) : ℝ) ≤
      Real.rpow q ((δ + lam * A) * k * r) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hq)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by norm_num) hq)
  have htwo : ((2 ^ C : ℕ) : ℝ) ≤ Real.rpow q (lam * C) := by
    calc
      ((2 ^ C : ℕ) : ℝ) = (2 : ℝ) ^ C := by norm_cast
      _ ≤ (Real.rpow q lam) ^ C := by gcongr
      _ = Real.rpow q (lam * C) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul hq0.le lam C).symm
  have hHpow : ((H ^ k : ℕ) : ℝ) ≤ Real.rpow q ((δ * r) * k) := by
    calc
      ((H ^ k : ℕ) : ℝ) = (H : ℝ) ^ k := by norm_cast
      _ ≤ (Real.rpow q (δ * r)) ^ k := by gcongr
      _ = Real.rpow q ((δ * r) * k) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul hq0.le (δ * r) k).symm
  have hmul : ((2 ^ C * H ^ k : ℕ) : ℝ) ≤
      Real.rpow q (lam * C + (δ * r) * k) := by
    rw [Nat.cast_mul]
    calc
      ((2 ^ C : ℕ) : ℝ) * ((H ^ k : ℕ) : ℝ) ≤
          Real.rpow q (lam * C) * Real.rpow q ((δ * r) * k) := by
        exact mul_le_mul htwo hHpow (by positivity)
          (Real.rpow_nonneg hq0.le _)
      _ = Real.rpow q (lam * C + (δ * r) * k) :=
        (Real.rpow_add hq0 _ _).symm
  have hCReal : (C : ℝ) ≤ A * k * r := by exact_mod_cast hC
  have hexp : lam * C + (δ * r) * k ≤ (δ + lam * A) * k * r := by
    calc
      lam * C + (δ * r) * k ≤ lam * (A * k * r) + (δ * r) * k := by
        gcongr
      _ = (δ + lam * A) * k * r := by ring
  exact hmul.trans (Real.rpow_le_rpow_of_exponent_le hq1 hexp)

private theorem roth_univariate_small_hasse (θ : ℝ) (hθ : 0 < θ)
    (P : ℤ[X]) (q : ℚ) (r : ℕ) (hr : 0 < r) (hq : 2 ≤ q.den)
    (hPne : P ≠ 0) (hheight : (rothPolyL1 P : ℝ) ≤
      Real.rpow q.den ((θ / 4) * r)) :
    ∃ a : ℕ, (a : ℝ) / r < θ ∧
      (Polynomial.hasseDeriv a (Polynomial.map (algebraMap ℤ ℚ) P)).eval q ≠ 0 := by
  let k : ℕ := ⌈θ * r⌉₊
  by_contra hnot
  push Not at hnot
  have hzero : ∀ a < k,
      (Polynomial.hasseDeriv a (Polynomial.map (algebraMap ℤ ℚ) P)).eval q = 0 := by
    intro a ha
    apply hnot a
    have haθ : (a : ℝ) < θ * r := Nat.lt_ceil.mp ha
    exact (div_lt_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2 (by
      simpa [mul_comm] using haθ)
  have hdivQ := roth_X_sub_C_pow_dvd_of_hasse_eval_eq_zero
    (Polynomial.map (algebraMap ℤ ℚ) P) q k hzero
  have hdiv := roth_rat_linear_pow_dvd_of_map_dvd P q k hdivQ
  have hlead : (P.leadingCoeff.natAbs : ℝ) ≤
      Real.rpow q.den ((θ / 4) * r) := by
    have hnat : P.leadingCoeff.natAbs ≤ rothPolyL1 P := by
      simpa using rothPolyL1_coeff_le P P.natDegree
    have hreal : (P.leadingCoeff.natAbs : ℝ) ≤ rothPolyL1 P := by
      exact_mod_cast hnat
    exact hreal.trans hheight
  have hindex := roth_univariate_index_le P q k r (θ / 4)
    hPne hq hr hdiv hlead
  have hceil : θ ≤ (k : ℝ) / r := by
    apply (le_div_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2
    simpa [k, mul_comm] using (Nat.le_ceil (θ * (r : ℝ)))
  linarith

structure RothLemmaInput (n : ℕ) (δ : ℝ) (Q R : ℕ) where
  P : MvPolynomial (Fin (n + 1)) ℤ
  r : Fin (n + 1) → ℕ
  q : Fin (n + 1) → ℚ
  P_ne : P ≠ 0
  P_degree : rothDegreeBound P r
  r_large : ∀ h, R ≤ r h
  den_large : Q ≤ (q 0).den
  den_monotone : Monotone fun h ↦ (q h).den
  r_antitone : Antitone r
  separated : ∀ i : Fin n, (r i.succ : ℝ) ≤ δ * r i.castSucc
  den_power : ∀ h, (q 0).den ^ r 0 ≤ (q h).den ^ r h
  height : (rothMvL1 P : ℝ) ≤ Real.rpow (q 0).den (δ * r 0)

private theorem rothMvWeight_le_order_div {m b : ℕ}
    (r : Fin m → ℕ) (i : RothMvIndex m) (hb : 0 < b)
    (hbr : ∀ h, b ≤ r h) :
    rothMvWeight r i ≤ (rothMvOrder i : ℝ) / b := by
  unfold rothMvWeight rothMvOrder
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro h _hh
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hrR : (b : ℝ) ≤ r h := by exact_mod_cast hbr h
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hbR hrR

private theorem rothLastSlice_zero_ne
    (P : MvPolynomial (Fin 1) ℤ) (hP : P ≠ 0) :
    rothLastSlice P (0 : RothMvIndex 0) ≠ 0 := by
  intro hzero
  apply hP
  ext d
  have htail : rothLastTail d = (0 : RothMvIndex 0) := Subsingleton.elim _ _
  rw [← rothLastIndex_eta d, htail, ← rothLastSlice_coeff, hzero]
  simp

private theorem roth_exists_nonzero_hasse_of_not_vanishesBelow
    {m : ℕ} {P : MvPolynomial (Fin m) ℚ} {x : Fin m → ℚ}
    {r : Fin m → ℕ} {T : ℝ}
    (h : ¬rothMvVanishesBelow P x r T) :
    ∃ i : RothMvIndex m, rothMvWeight r i < T ∧
      MvPolynomial.eval x (rothMvHasse i P) ≠ 0 := by
  rw [rothMvVanishesBelow] at h
  push Not at h
  obtain ⟨i, hi, hne⟩ := h
  refine ⟨i, hi, ?_⟩
  simpa [rothTranslate_coeff_eq_eval_hasse] using hne

private theorem roth_lemma_base (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    ∃ (δ : ℝ) (Q R : ℕ), 0 < δ ∧ δ ≤ 1 ∧ 2 ≤ Q ∧ 1 ≤ R ∧
      ∀ A : RothLemmaInput 0 δ Q R,
        ¬rothMvVanishesBelow
          (MvPolynomial.map (algebraMap ℤ ℚ) A.P) A.q A.r θ := by
  let δ := θ / 8
  obtain ⟨Q, hQtwo, hQ⟩ := roth_exists_rpow_threshold (by
    dsimp [δ]
    positivity : 0 < δ)
  refine ⟨δ, Q, 1, by dsimp [δ]; positivity, by dsimp [δ]; linarith,
    hQtwo, le_rfl, fun A hvan ↦ ?_⟩
  have hr : 0 < A.r 0 := lt_of_lt_of_le Nat.zero_lt_one (A.r_large 0)
  have hq : 2 ≤ (A.q 0).den := hQtwo.trans A.den_large
  let Pu := rothLastSlice A.P (0 : RothMvIndex 0)
  have hPu : Pu ≠ 0 := rothLastSlice_zero_ne A.P A.P_ne
  have hPul1Nat : rothPolyL1 Pu ≤ 2 ^ A.r 0 * rothMvL1 A.P := by
    calc
      rothPolyL1 Pu ≤ (A.r (Fin.last 0) + 1) * rothMvL1 A.P :=
        rothPolyL1_lastSlice_le A.P_degree 0
      _ ≤ 2 ^ A.r 0 * rothMvL1 A.P := by
        gcongr
        simpa using roth_succ_le_two_pow hr
  have hPul1 : (rothPolyL1 Pu : ℝ) ≤
      Real.rpow (A.q 0).den ((θ / 4) * A.r 0) := by
    have habsorb := roth_absorb_height (A.q 0).den (rothMvL1 A.P)
      (A.r 0) 1 (A.r 0) 1 δ δ hq (by positivity) (hQ _ A.den_large)
      A.height (by simp)
    have hnat : (rothPolyL1 Pu : ℝ) ≤
        ((2 ^ A.r 0 * rothMvL1 A.P ^ 1 : ℕ) : ℝ) := by
      exact_mod_cast (hPul1Nat.trans_eq (by simp))
    refine hnat.trans ?_
    have hexp : (δ + δ * (1 : ℕ)) * (1 : ℕ) * A.r 0 =
        (θ / 4) * A.r 0 := by
      dsimp [δ]
      push_cast
      ring
    rwa [hexp] at habsorb
  obtain ⟨a, haweight, hane⟩ :=
    roth_univariate_small_hasse θ hθ Pu (A.q 0) (A.r 0) hr hq hPu hPul1
  let i := rothLastIndex (0 : RothMvIndex 0) a
  have hiweight : rothMvWeight A.r i < θ := by
    rw [rothMvWeight_lastIndex]
    simpa [i, rothMvWeight] using haweight
  have hz := hvan i hiweight
  rw [rothTranslate_coeff_eq_eval_hasse] at hz
  have hqfun : A.q = Fin.lastCases (A.q (Fin.last 0)) (fun _ ↦ 0) := by
    funext h
    have hh : h = Fin.last 0 := Fin.ext (by simp)
    subst h
    exact (Fin.lastCases_last (motive := fun _ : Fin 1 ↦ ℚ)
      (last := A.q (Fin.last 0))
      (cast := fun _ : Fin 0 ↦ (0 : ℚ))).symm
  apply hane
  dsimp [Pu]
  have hqzero : A.q 0 = A.q (Fin.last 0) := by
    exact congrArg A.q (Fin.ext (by simp))
  rw [hqzero]
  calc
    ((Polynomial.hasseDeriv a
        (Polynomial.map (algebraMap ℤ ℚ)
          (rothLastSlice A.P (0 : RothMvIndex 0)))).eval (A.q (Fin.last 0))) =
        MvPolynomial.eval (Fin.lastCases (A.q (Fin.last 0)) (fun _ ↦ 0))
          (rothMvHasse (rothLastIndex (0 : RothMvIndex 0) a)
            (MvPolynomial.map (algebraMap ℤ ℚ) A.P)) :=
      (rothLastSlice_hasse_eval A.P (0 : RothMvIndex 0) a
        (A.q (Fin.last 0))).symm
    _ = 0 := by
      rw [← hqfun]
      simpa [i] using hz

private theorem roth_rpow_of_nat_pow_le (a b ra rb : ℕ) (c : ℝ)
    (hc : 0 ≤ c) (hab : a ^ ra ≤ b ^ rb) :
    Real.rpow a (c * ra) ≤ Real.rpow b (c * rb) := by
  have habR : ((a ^ ra : ℕ) : ℝ) ≤ (b ^ rb : ℕ) := by exact_mod_cast hab
  calc
    Real.rpow a (c * ra) = Real.rpow a ((ra : ℝ) * c) := by ring_nf
    _ = Real.rpow (Real.rpow a (ra : ℝ)) c :=
      Real.rpow_mul (Nat.cast_nonneg _) _ _
    _ = Real.rpow (a ^ ra : ℕ) c := by
      congr 1
      exact (Real.rpow_natCast (a : ℝ) ra).trans (by norm_cast)
    _ ≤ Real.rpow (b ^ rb : ℕ) c :=
      Real.rpow_le_rpow (by positivity) habR hc
    _ = Real.rpow (Real.rpow b (rb : ℝ)) c := by
      congr 1
      exact ((Real.rpow_natCast (b : ℝ) rb).trans (by norm_cast)).symm
    _ = Real.rpow b ((rb : ℝ) * c) :=
      (Real.rpow_mul (Nat.cast_nonneg _) _ _).symm
    _ = Real.rpow b (c * rb) := by ring_nf

private theorem roth_lemma :
    ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ ≤ 1 →
      ∃ (δ : ℝ) (Q R : ℕ), 0 < δ ∧ δ ≤ 1 ∧ 2 ≤ Q ∧ 1 ≤ R ∧
        ∀ A : RothLemmaInput n δ Q R,
          ¬rothMvVanishesBelow
            (MvPolynomial.map (algebraMap ℤ ℚ) A.P) A.q A.r θ := by
  intro n
  induction n with
  | zero =>
      intro θ hθ hθone
      exact roth_lemma_base θ hθ hθone
  | succ n ih =>
      intro θ hθ hθone
      let τ := θ ^ 2 / 256
      have hτ : 0 < τ := by dsimp [τ]; positivity
      have hτone : τ ≤ 1 := by
        dsimp [τ]
        nlinarith [sq_nonneg (θ - 1), sq_nonneg θ]
      obtain ⟨δI, QI, RI, hδI, hδIone, hQItwo, hRIone, hIH⟩ :=
        ih τ hτ hτone
      let δu := τ / 4
      let δc := min δI δu
      let A0 : ℕ := n + 6
      let lam := δc / (4 * (A0 : ℝ))
      have hδu : 0 < δu := by dsimp [δu]; positivity
      have hδc : 0 < δc := lt_min hδI hδu
      have hA0 : 0 < A0 := by dsimp [A0]; omega
      have hlam : 0 < lam := by dsimp [lam]; positivity
      obtain ⟨QA, hQAtwo, hQA⟩ := roth_exists_rpow_threshold hlam
      let δ := min (θ / 4) (δc / 4)
      let Q := max QI QA
      let R := max RI (max 1 ⌈16 / θ⌉₊)
      have hδ : 0 < δ := lt_min (by positivity) (by positivity)
      have hδtheta : δ ≤ θ / 4 := min_le_left _ _
      have hδc_le : δ ≤ δc / 4 := min_le_right _ _
      have hδI_le : δ ≤ δI :=
        hδc_le.trans (by
          have := min_le_left δI δu
          linarith)
      have hδu_le : δ ≤ δu :=
        hδc_le.trans (by
          have := min_le_right δI δu
          linarith)
      have hmargin : δ + lam * A0 ≤ δc / 2 := by
        have hA0R : (0 : ℝ) < A0 := by exact_mod_cast hA0
        have hlamA : lam * A0 = δc / 4 := by
          dsimp [lam]
          field_simp
        rw [hlamA]
        linarith
      have hmarginI : δ + lam * A0 ≤ δI :=
        hmargin.trans (by
          have := min_le_left δI δu
          linarith)
      have hmarginU : δ + lam * A0 ≤ δu :=
        hmargin.trans (by
          have := min_le_right δI δu
          linarith)
      refine ⟨δ, Q, R, hδ, hδtheta.trans (by linarith),
        hQItwo.trans (le_max_left _ _), le_max_of_le_right (le_max_left _ _),
        fun X hvan ↦ ?_⟩
      have hQXI : QI ≤ (X.q 0).den :=
        (le_max_left QI QA).trans X.den_large
      have hQXA : QA ≤ (X.q 0).den :=
        (le_max_right QI QA).trans X.den_large
      have hq0 : 2 ≤ (X.q 0).den := hQItwo.trans hQXI
      have hrpos : ∀ h, 0 < X.r h := fun h ↦
        lt_of_lt_of_le Nat.zero_lt_one ((le_max_of_le_right (le_max_left _ _)).trans
          (X.r_large h))
      obtain ⟨d⟩ := roth_exists_determinant_data X.P X.r X.P_ne X.P_degree
      obtain ⟨e⟩ := roth_exists_integral_factor_data d
      let r0 := X.r 0
      let rlast := X.r (Fin.last (n + 1))
      have hrlast : 0 < rlast := hrpos _
      have hrlast0 : rlast ≤ r0 := X.r_antitone (Fin.zero_le _)
      have hk0 : d.k ≤ 2 * r0 := by
        calc
          d.k ≤ rlast + 1 := d.k_le
          _ ≤ r0 + 1 := Nat.add_le_add_right hrlast0 1
          _ ≤ 2 * r0 := by omega
      have hsumFirst : (∑ h : Fin (n + 1), X.r h.castSucc) ≤ (n + 1) * r0 := by
        calc
          (∑ h : Fin (n + 1), X.r h.castSucc) ≤ ∑ _h : Fin (n + 1), r0 := by
            gcongr with h
            exact X.r_antitone (Fin.zero_le _)
          _ = (n + 1) * r0 := by simp
      have hsumAll : (∑ h, X.r h) ≤ (n + 2) * r0 := by
        calc
          (∑ h, X.r h) ≤ ∑ _h : Fin (n + 2), r0 := by
            gcongr with h
            exact X.r_antitone (Fin.zero_le _)
          _ = (n + 2) * r0 := by simp
      let CV := d.k * d.k + d.k * (∑ h : Fin (n + 1), X.r h.castSucc)
      let CW := d.k * rlast + d.k * d.k + d.k * (∑ h, X.r h)
      have hCV : CV ≤ A0 * d.k * r0 := by
        calc
          CV ≤ d.k * (2 * r0) + d.k * ((n + 1) * r0) := by
            dsimp [CV]
            exact Nat.add_le_add (Nat.mul_le_mul_left d.k hk0)
              (Nat.mul_le_mul_left d.k hsumFirst)
          _ = (n + 3) * d.k * r0 := by ring
          _ ≤ A0 * d.k * r0 := by
            gcongr
            dsimp [A0]
            omega
      have hCW : CW ≤ A0 * d.k * r0 := by
        calc
          CW ≤ d.k * r0 + d.k * (2 * r0) + d.k * ((n + 2) * r0) := by
            dsimp [CW]
            exact Nat.add_le_add
              (Nat.add_le_add (Nat.mul_le_mul_left d.k hrlast0)
                (Nat.mul_le_mul_left d.k hk0))
              (Nat.mul_le_mul_left d.k hsumAll)
          _ = (n + 5) * d.k * r0 := by ring
          _ ≤ A0 * d.k * r0 := by
            gcongr
            dsimp [A0]
            omega
      have hVheight : (rothMvL1 d.V : ℝ) ≤
          Real.rpow (X.q 0).den (δI * (d.k * r0)) := by
        have hcoarseNat := roth_determinant_V_l1_coarse d
        have hcoarse : (rothMvL1 d.V : ℝ) ≤
            ((2 ^ CV * rothMvL1 X.P ^ d.k : ℕ) : ℝ) := by
          exact_mod_cast hcoarseNat
        have habsorb := roth_absorb_height (X.q 0).den (rothMvL1 X.P)
          CV d.k r0 A0 δ lam hq0 hlam.le (hQA _ hQXA) X.height hCV
        refine hcoarse.trans (habsorb.trans ?_)
        apply Real.rpow_le_rpow_of_exponent_le (by
          exact_mod_cast (show 1 ≤ (X.q 0).den by omega) : (1 : ℝ) ≤ (X.q 0).den)
        have hk0R : (0 : ℝ) ≤ d.k * r0 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hmarginI hk0R]
      let rV : Fin (n + 1) → ℕ := fun h ↦ d.k * X.r h.castSucc
      let qV : Fin (n + 1) → ℚ := fun h ↦ X.q h.castSucc
      let B : RothLemmaInput n δI QI RI := {
        P := d.V
        r := rV
        q := qV
        P_ne := d.V_ne
        P_degree := d.V_degree
        r_large := fun h ↦ by
          have hrh : RI ≤ X.r h.castSucc :=
            (le_max_left RI (max 1 ⌈16 / θ⌉₊)).trans (X.r_large h.castSucc)
          dsimp [rV]
          nlinarith [d.k_pos]
        den_large := by simpa [qV] using hQXI
        den_monotone := fun i j hij ↦
          X.den_monotone (Fin.castSucc_le_castSucc_iff.mpr hij)
        r_antitone := fun i j hij ↦ by
          dsimp [rV]
          exact Nat.mul_le_mul_left d.k
            (X.r_antitone (Fin.castSucc_le_castSucc_iff.mpr hij))
        separated := fun i ↦ by
          have hp := X.separated i.castSucc
          dsimp [rV]
          push_cast
          have hkR : (0 : ℝ) ≤ d.k := by positivity
          have hki : (0 : ℝ) ≤ d.k * X.r i.castSucc.castSucc := by positivity
          calc
            (d.k : ℝ) * X.r i.succ.castSucc =
                (d.k : ℝ) * X.r i.castSucc.succ := by rw [Fin.succ_castSucc]
            _ ≤ (d.k : ℝ) * (δ * X.r i.castSucc.castSucc) :=
              mul_le_mul_of_nonneg_left hp hkR
            _ = δ * ((d.k : ℝ) * X.r i.castSucc.castSucc) := by ring
            _ ≤ δI * ((d.k : ℝ) * X.r i.castSucc.castSucc) :=
              mul_le_mul_of_nonneg_right hδI_le hki
        den_power := fun h ↦ by
          have hp := X.den_power h.castSucc
          dsimp [qV, rV]
          calc
            (X.q 0).den ^ (d.k * X.r 0) =
                ((X.q 0).den ^ X.r 0) ^ d.k := by rw [mul_comm, pow_mul]
            _ ≤ ((X.q h.castSucc).den ^ X.r h.castSucc) ^ d.k := by gcongr
            _ = (X.q h.castSucc).den ^ (d.k * X.r h.castSucc) := by
              rw [mul_comm, pow_mul]
        height := by simpa [rV, qV, r0, mul_assoc] using hVheight
      }
      have hVnot := hIH B
      obtain ⟨iV, hiVweight, hiVne⟩ :=
        roth_exists_nonzero_hasse_of_not_vanishesBelow hVnot
      have hWheight0 : (rothPolyL1 e.WZ : ℝ) ≤
          Real.rpow (X.q 0).den (δu * (d.k * r0)) := by
        have hcoarseNat := roth_determinant_W_l1_coarse d e hrlast
        have hcoarse : (rothPolyL1 e.WZ : ℝ) ≤
            ((2 ^ CW * rothMvL1 X.P ^ d.k : ℕ) : ℝ) := by
          exact_mod_cast hcoarseNat
        have habsorb := roth_absorb_height (X.q 0).den (rothMvL1 X.P)
          CW d.k r0 A0 δ lam hq0 hlam.le (hQA _ hQXA) X.height hCW
        refine hcoarse.trans (habsorb.trans ?_)
        apply Real.rpow_le_rpow_of_exponent_le (by
          exact_mod_cast (show 1 ≤ (X.q 0).den by omega) : (1 : ℝ) ≤ (X.q 0).den)
        have hk0R : (0 : ℝ) ≤ d.k * r0 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hmarginU hk0R]
      have hWheight : (rothPolyL1 e.WZ : ℝ) ≤
          Real.rpow (X.q (Fin.last (n + 1))).den
            ((τ / 4) * (d.k * rlast)) := by
        refine hWheight0.trans ?_
        have hp := X.den_power (Fin.last (n + 1))
        have ht := roth_rpow_of_nat_pow_le (X.q 0).den
          (X.q (Fin.last (n + 1))).den r0 rlast (δu * d.k)
          (by positivity) hp
        simpa [δu, Nat.cast_mul, mul_assoc] using ht
      have hqlast : 2 ≤ (X.q (Fin.last (n + 1))).den :=
        hq0.trans (X.den_monotone (Fin.zero_le _))
      obtain ⟨aW, haWweight, haWne⟩ := roth_univariate_small_hasse τ hτ e.WZ
        (X.q (Fin.last (n + 1))) (d.k * rlast) (Nat.mul_pos d.k_pos hrlast)
        hqlast e.WZ_ne (by simpa [Nat.cast_mul] using hWheight)
      let rprev := X.r (Fin.last n).castSucc
      have hrprev : 0 < rprev := hrpos _
      have hprefixMin : ∀ h : Fin (n + 1), rprev ≤ X.r h.castSucc := by
        intro h
        exact X.r_antitone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last h))
      have hrowWeight : ∀ s, rothMvWeight (fun h ↦ X.r h.castSucc) (d.row s) ≤ δ := by
        intro s
        calc
          rothMvWeight (fun h ↦ X.r h.castSucc) (d.row s) ≤
              (rothMvOrder (d.row s) : ℝ) / rprev :=
            rothMvWeight_le_order_div _ _ hrprev hprefixMin
          _ ≤ (s : ℝ) / rprev := by
            gcongr
            exact_mod_cast d.row_order s
          _ ≤ (rlast : ℝ) / rprev := by
            gcongr
            have hkLast : d.k ≤ rlast + 1 := by simpa [rlast] using d.k_le
            have hsNat : s.val ≤ rlast := by omega
            exact_mod_cast hsNat
          _ ≤ δ := by
            apply (div_le_iff₀ (by exact_mod_cast hrprev : (0 : ℝ) < rprev)).2
            simpa [rprev, rlast] using
              X.separated (Fin.last n)
      let u : Fin d.k → RothMvIndex (n + 2) :=
        fun s ↦ rothLastIndex (d.row s) 0
      let v : Fin d.k → RothMvIndex (n + 2) :=
        fun t ↦ rothLastIndex 0 t.val
      let L : ℝ := ∑ t : Fin d.k, max 0 (θ - δ - (t : ℝ) / rlast)
      have hrowWeightFull : ∀ s, rothMvWeight X.r (u s) ≤ δ := by
        intro s
        rw [rothMvWeight_lastIndex]
        simpa [u, rothMvWeight] using hrowWeight s
      have hdetVan := rothHasseDet_vanishesBelow_of_rowWeight_le
        hvan u v hrowWeightFull
      have hvweight : ∀ t : Fin d.k,
          rothMvWeight X.r (v t) = (t : ℝ) / rlast := by
        intro t
        rw [rothMvWeight_lastIndex]
        simp [rlast, rothMvWeight]
      simp_rw [hvweight] at hdetVan
      have hmapU : MvPolynomial.map (algebraMap ℤ ℚ) d.U =
          rothHasseDet (MvPolynomial.map (algebraMap ℤ ℚ) X.P) u v := by
        rw [d.U_def, rothHasseDet_map]
      rw [← hmapU] at hdetVan
      change rothMvVanishesBelow
        (MvPolynomial.map (algebraMap ℤ ℚ) d.U) X.q X.r L at hdetVan
      have hscaledVan0 := rothMvVanishesBelow_smul hdetVan
        (d.V.coeff e.coeffIndex : ℚ)
      have hscaledVan := rothMvVanishesBelow_mul_weights hscaledVan0 d.k_pos hrpos
      have hrlarge : 16 ≤ θ * rlast := by
        have hceil : 16 / θ ≤ (⌈16 / θ⌉₊ : ℝ) := Nat.le_ceil _
        have hRlast : ⌈16 / θ⌉₊ ≤ rlast :=
          (le_max_of_le_right (le_max_right 1 ⌈16 / θ⌉₊)).trans
            (X.r_large (Fin.last (n + 1)))
        have hcast : (⌈16 / θ⌉₊ : ℝ) ≤ rlast := by exact_mod_cast hRlast
        have := hceil.trans hcast
        calc
          (16 : ℝ) = θ * (16 / θ) := by field_simp
          _ ≤ θ * rlast := mul_le_mul_of_nonneg_left this hθ.le
      have htri : θ ^ 2 / 64 ≤ L / d.k := by
        exact roth_triangular_sum_lower hθ hθone hδtheta hrlast hrlarge
          d.k_pos d.k_le
      have hsmall : 2 * τ < L / d.k := by
        have : 2 * τ < θ ^ 2 / 64 := by
          dsimp [τ]
          nlinarith [sq_pos_of_pos hθ]
        exact this.trans_le htri
      let qV' : Fin (n + 1) → ℚ := fun h ↦ X.q h.castSucc
      have hqeta : X.q = Fin.lastCases (X.q (Fin.last (n + 1))) qV' := by
        funext h
        refine Fin.lastCases ?_ (fun j ↦ ?_) h
        · exact (Fin.lastCases_last (motive := fun _ : Fin (n + 2) ↦ ℚ)
            (last := X.q (Fin.last (n + 1))) (cast := qV')).symm
        · exact (Fin.lastCases_castSucc (motive := fun _ : Fin (n + 2) ↦ ℚ)
            (last := X.q (Fin.last (n + 1))) (cast := qV') j).symm
      have hfullne :
          MvPolynomial.eval X.q
            (rothMvHasse (rothLastIndex iV aW)
              ((d.V.coeff e.coeffIndex : ℚ) •
                MvPolynomial.map (algebraMap ℤ ℚ) d.U)) ≠ 0 := by
        rw [hqeta]
        rw [rothMvHasse_eval_last_of_factorization _ _ _ e.scaled_factorization]
        exact mul_ne_zero hiVne haWne
      have hiweight : rothMvWeight (fun h ↦ d.k * X.r h)
          (rothLastIndex iV aW) < L / d.k := by
        rw [rothMvWeight_lastIndex]
        change rothMvWeight rV iV < τ at hiVweight
        have haWweight' : (aW : ℝ) / ((d.k : ℝ) * rlast) < τ := by
          simpa [Nat.cast_mul] using haWweight
        have hadd : rothMvWeight rV iV +
            (aW : ℝ) / (d.k * rlast) < 2 * τ := by
          nlinarith
        simpa [rV, rlast, Nat.cast_mul] using hadd.trans hsmall
      have hz := hscaledVan (rothLastIndex iV aW) hiweight
      rw [rothTranslate_coeff_eq_eval_hasse] at hz
      exact hfullne hz

private theorem roth_ridout_exists_approximation_chain {α p : ℝ} (hp : 0 < p)
    (A : Set ℚ)
    (hA : A ⊆ {q : ℚ | |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p})
    (hinf : A.Infinite) (m N K : ℕ) :
    ∃ q : Fin (m + 1) → ℚ,
      (∀ h, q h ∈ A) ∧
      N < (q 0).den ∧
      ∀ h : Fin m, (q h.castSucc).den ^ K < (q h.succ).den := by
  induction m with
  | zero =>
      obtain ⟨a, ha, hN⟩ := roth_ridout_exists_approx_den_gt hp A hA hinf N
      let q : Fin 1 → ℚ := fun _ ↦ a
      exact ⟨q, fun _ ↦ ha, by simpa [q] using hN, fun h ↦ Fin.elim0 h⟩
  | succ m ih =>
      obtain ⟨q, hq, hqN, hchain⟩ := ih
      obtain ⟨a, ha, hlast⟩ := roth_ridout_exists_approx_den_gt hp A hA hinf
        ((q (Fin.last m)).den ^ K)
      let q' : Fin (m + 2) → ℚ := Fin.lastCases a q
      refine ⟨q', ?_, ?_, ?_⟩
      · intro h
        refine Fin.lastCases ?_ (fun j ↦ ?_) h
        · simpa [q'] using ha
        · simpa [q'] using hq j
      · change N < (q' (0 : Fin (m + 2))).den
        simpa only [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc by rfl,
          q', Fin.lastCases_castSucc] using hqN
      · intro h
        refine Fin.lastCases ?_ (fun j ↦ ?_) h
        · simpa [q'] using hlast
        · simpa only [q', Fin.lastCases_castSucc, Fin.succ_castSucc] using hchain j

end MathlibExt.NumberTheory.RothAuxiliary
