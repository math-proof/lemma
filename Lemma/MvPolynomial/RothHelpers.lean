import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary

namespace MvPolynomial

lemma rothMvHasse_monomial_h {m : ℕ} {R : Type*} [CommSemiring R]
    (i j : RothMvIndex m) (c : R) :
    rothMvHasse i (MvPolynomial.monomial j c) =
      MvPolynomial.monomial (j - i) ((∏ h, (Nat.choose (j h) (i h) : R)) * c) := by
  simp [rothMvHasse]

lemma rothMvHasse_zero_h {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) : rothMvHasse i (0 : MvPolynomial (Fin m) R) = 0 := by
  simp [rothMvHasse]

lemma rothMvHasse_zero_index_h {m : ℕ} {R : Type*} [CommSemiring R]
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

lemma rothMvHasse_coeff_h {m : ℕ} {R : Type*} [CommSemiring R]
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

lemma rothMvHasse_add_h {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) (P Q : MvPolynomial (Fin m) R) :
    rothMvHasse i (P + Q) = rothMvHasse i P + rothMvHasse i Q := by
  ext k
  simp only [rothMvHasse_coeff_h, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    mul_add]

lemma rothMvHasse_map_h {m : ℕ} {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (i : RothMvIndex m)
    (P : MvPolynomial (Fin m) R) :
    MvPolynomial.map f (rothMvHasse i P) =
      rothMvHasse i (MvPolynomial.map f P) := by
  ext k
  rw [MvPolynomial.coeff_map, rothMvHasse_coeff_h, rothMvHasse_coeff_h,
    MvPolynomial.coeff_map, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro h _hh
  simp

lemma rothMvHasse_finset_sum_h {m : ℕ} {R : Type*} [CommSemiring R]
    {ι : Type*} (s : Finset ι) (i : RothMvIndex m)
    (P : ι → MvPolynomial (Fin m) R) :
    rothMvHasse i (∑ a ∈ s, P a) = ∑ a ∈ s, rothMvHasse i (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothMvHasse_zero_h]
  | @insert a s ha ih => simp [ha, rothMvHasse_add_h, ih]

lemma rothTranslate_C_h {R : Type*} [CommRing R] :
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

lemma rothTranslate_coeff_cons_h {R : Type*} [CommRing R] {n : ℕ}
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

lemma rothMvHasse_finSucc_coeff_h {n : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin (n + 1)) R) (a k : ℕ) (i : RothMvIndex n) :
    ((MvPolynomial.finSuccEquiv R n) (rothMvHasse (i.cons a) P)).coeff k =
      rothMvHasse i
        ((Polynomial.hasseDeriv a ((MvPolynomial.finSuccEquiv R n) P)).coeff k) := by
  ext l
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [show (i.cons a : RothMvIndex (n + 1)) = Finsupp.cons a i from rfl]
  rw [show (l.cons k : RothMvIndex (n + 1)) = Finsupp.cons k l from rfl]
  rw [rothMvHasse_coeff_h, rothMvHasse_coeff_h, Polynomial.hasseDeriv_coeff]
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

lemma rothTranslate_eval_coeff_h {R : Type*} [CommRing R] {m : ℕ}
    (x : Fin m → R) (p : Polynomial (MvPolynomial (Fin m) R)) (y : R)
    (i : RothMvIndex m) :
    (rothTranslate m x (Polynomial.eval (MvPolynomial.C y) p)).coeff i =
      ∑ k ∈ p.support, (rothTranslate m x (p.coeff k)).coeff i * y ^ k := by
  rw [Polynomial.eval_eq_sum]
  rw [Polynomial.sum_def, map_sum, MvPolynomial.coeff_sum]
  congr with k
  rw [map_mul, map_pow, rothTranslate_C_h]
  rw [← MvPolynomial.C_pow, mul_comm, MvPolynomial.coeff_C_mul]
  ac_rfl

lemma rothTranslate_coeff_eq_eval_hasse_h {R : Type*} [CommRing R] :
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
      rw [rothMvHasse_zero_index_h]
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
      rw [← hi, rothTranslate_coeff_cons_h]
      change
        (rothTranslate n xt
          ((Polynomial.taylor (MvPolynomial.C (x 0)) p).coeff a)).coeff it = _
      rw [Polynomial.taylor_coeff]
      change (rothTranslate n xt (Polynomial.eval (MvPolynomial.C (x 0)) A)).coeff it = _
      rw [rothTranslate_eval_coeff_h]
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
        have hBk := rothMvHasse_finSucc_coeff_h P a k it
        change B.coeff k = rothMvHasse it (A.coeff k) at hBk
        rw [hAk, rothMvHasse_zero_h] at hBk
        exact (Polynomial.mem_support_iff.mp hk) hBk
      have hmap : (Polynomial.map (MvPolynomial.eval xt) B).support ⊆ A.support :=
        (Polynomial.support_map_subset (MvPolynomial.eval xt) B).trans hBA
      rw [Polynomial.eval_eq_sum]
      rw [Polynomial.sum_eq_of_subset (fun e c ↦ c * x 0 ^ e) (by simp) hmap]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Polynomial.coeff_map]
      have hBk := rothMvHasse_finSucc_coeff_h P a k it
      change B.coeff k = rothMvHasse it (A.coeff k) at hBk
      rw [hBk, ← ih xt (A.coeff k) it]


lemma rothMvHasse_eval_ofCoeff_index_h {m : ℕ} {R : Type*} [CommRing R]
    {r : Fin m → ℕ} (c : RothCoeff r) (i : RothMvIndex m) (x : Fin m → R) :
    MvPolynomial.eval₂ (algebraMap ℤ R) x (rothMvHasse i (rothMvOfCoeff c)) =
      rothHasseEval c (fun h ↦ i h) x := by
  classical
  rw [rothMvOfCoeff, rothMvHasse_finset_sum_h Finset.univ]
  rw [MvPolynomial.eval₂_sum]
  unfold rothHasseEval
  apply Finset.sum_congr rfl
  intro j _hj
  rw [rothMvHasse_monomial_h, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype]
  · change
      (algebraMap ℤ R) ((∏ h, (Nat.choose (j h) (i h) : ℤ)) * c j) *
          ∏ h, x h ^ ((j h : ℕ) - i h) = _
    rw [map_mul, map_prod]
    rw [algebraMap_int_eq, Int.coe_castRingHom]
    dsimp only
    simp only [Int.cast_natCast]
    rw [Finset.prod_mul_distrib]
    ac_rfl
  · intro h
    simp


lemma roth_eval₂_rat_cast_h {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (q : Fin m → ℚ) :
    ((MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P : ℚ) : ℝ) =
      MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P := by
  change (algebraMap ℚ ℝ) (MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 2

lemma rothFinsuppL1_sum_superset_h {α : Type*} (f : α →₀ ℤ) (s : Finset α)
    (hfs : f.support ⊆ s) :
    rothFinsuppL1 f = ∑ a ∈ s, (f a).natAbs := by
  unfold rothFinsuppL1
  apply Finset.sum_subset hfs
  intro a ha hnot
  rw [Finsupp.notMem_support_iff.mp hnot]
  simp

lemma rothFinsuppL1_add_h {α : Type*} (f g : α →₀ ℤ) :
    rothFinsuppL1 (f + g) ≤ rothFinsuppL1 f + rothFinsuppL1 g := by
  classical
  let s := f.support ∪ g.support
  rw [rothFinsuppL1_sum_superset_h (f + g) s Finsupp.support_add]
  rw [rothFinsuppL1_sum_superset_h f s Finset.subset_union_left]
  rw [rothFinsuppL1_sum_superset_h g s Finset.subset_union_right]
  rw [← Finset.sum_add_distrib]
  gcongr with a ha
  exact Int.natAbs_add_le _ _

lemma rothFinsuppL1_single_h {α : Type*} (a : α) (c : ℤ) :
    rothFinsuppL1 (Finsupp.single a c) = c.natAbs := by
  classical
  by_cases hc : c = 0
  · simp [hc, rothFinsuppL1]
  · simp [rothFinsuppL1, hc]

lemma rothMvL1_monomial_h {m : ℕ} (i : RothMvIndex m) (c : ℤ) :
    rothMvL1 (MvPolynomial.monomial i c) = c.natAbs := by
  change rothFinsuppL1 (Finsupp.single i c) = c.natAbs
  exact rothFinsuppL1_single_h i c

lemma rothMvL1_add_h {m : ℕ} (P Q : MvPolynomial (Fin m) ℤ) :
    rothMvL1 (P + Q) ≤ rothMvL1 P + rothMvL1 Q :=
  rothFinsuppL1_add_h P.coeff Q.coeff

lemma rothMvL1_finset_sum_h {m : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial (Fin m) ℤ) :
    rothMvL1 (∑ a ∈ s, P a) ≤ ∑ a ∈ s, rothMvL1 (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothMvL1, rothFinsuppL1]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (rothFinsuppL1_add_h _ _).trans (Nat.add_le_add_left ih _)


lemma rothDegreeBoundOver_hasse_h {m : ℕ} {R : Type*} [CommSemiring R]
    {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ} (hP : rothDegreeBoundOver P r)
    (i : RothMvIndex m) :
    rothDegreeBoundOver (rothMvHasse i P) r := by
  intro k hk h
  have hcoeff := MvPolynomial.mem_support_iff.mp hk
  rw [rothMvHasse_coeff_h] at hcoeff
  have hPk : P.coeff (k + i) ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hz, mul_zero])
  have hmem : k + i ∈ P.support := MvPolynomial.mem_support_iff.mpr hPk
  exact (Nat.le_add_right (k h) (i h)).trans (hP (k + i) hmem h)

lemma rothMvL1_hasse_le_h {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
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
      rothMvL1_finset_sum_h P.support _
    _ = ∑ j ∈ P.support, (∏ h, Nat.choose (j h) (i h)) * (P.coeff j).natAbs := by
      congr with j
      rw [rothMvL1_monomial_h, Int.natAbs_mul, ← Nat.cast_prod, Int.natAbs_natCast]
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

lemma roth_abs_eval₂_le_l1_h {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (x : Fin m → ℝ) (r : Fin m → ℕ) (hP : rothDegreeBound P r) :
    |MvPolynomial.eval₂ (algebraMap ℤ ℝ) x P| ≤
      (rothMvL1 P : ℝ) * ∏ h, max 1 |x h| ^ r h := by
  classical
  rw [MvPolynomial.eval₂_eq']
  calc
    |∑ d ∈ P.support,
        (algebraMap ℤ ℝ) (P.coeff d) * ∏ h, x h ^ d h| ≤
        ∑ d ∈ P.support,
          |(algebraMap ℤ ℝ) (P.coeff d) * ∏ h, x h ^ d h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support,
          ((P.coeff d).natAbs : ℝ) * ∏ h, max 1 |x h| ^ r h := by
      gcongr with d hd
      rw [abs_mul, Finset.abs_prod]
      have hcoeff : |(algebraMap ℤ ℝ) (P.coeff d)| = ((P.coeff d).natAbs : ℝ) := by
        rw [algebraMap_int_eq, Int.coe_castRingHom]
        norm_num
      rw [hcoeff]
      gcongr with h
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (le_max_right 1 |x h|) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (hP d hd h))
    _ = (rothMvL1 P : ℝ) * ∏ h, max 1 |x h| ^ r h := by
      rw [← Finset.sum_mul]
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support]
      norm_cast

end MvPolynomial
