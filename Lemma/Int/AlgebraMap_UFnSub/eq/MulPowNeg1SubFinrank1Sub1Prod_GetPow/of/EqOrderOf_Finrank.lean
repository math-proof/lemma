import Mathlib
import sympy.Basic

open Polynomial Module

/--
[AlgEquiv_algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgEquiv_algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank.lean)
-/

noncomputable def T
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (c : E) : Module.End F E :=
  (σ.symm : E →ₐ[F] E).toLinearMap ∘ₗ LinearMap.mulLeft F c

noncomputable def cf
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (c : E) (i : ℕ) : E := ∏ j ∈ Finset.range i, (σ.symm ^ (j + 1)) c

private lemma T_apply
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (c y : E) : T σ c y = σ.symm (c * y) := rfl

private lemma cf_zero
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (c : E) : cf σ c 0 = 1 := by simp [cf]

private lemma cf_succ
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (c : E) (i : ℕ) : cf σ c (i + 1) = σ.symm c * σ.symm (cf σ c i) := by
  unfold cf
  rw [Finset.prod_range_succ', zero_add, pow_one, map_prod, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← AlgEquiv.mul_apply, ← pow_succ']

private lemma cf_ne_zero
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  {c : E} (hc : c ≠ 0) (i : ℕ) : cf σ c i ≠ 0 := by
  unfold cf
  exact Finset.prod_ne_zero_iff.2 fun j _ => (map_ne_zero_iff _ (σ.symm ^ (j + 1)).injective).2 hc

private lemma T_pow_apply
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (c : E) (i : ℕ) (y : E) : (T σ c ^ i) y = cf σ c i * (σ.symm ^ i) y := by
  induction i generalizing y with
  | zero => simp [cf_zero]
  | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih, T_apply, map_mul, map_mul, cf_succ, pow_succ',
        AlgEquiv.mul_apply]
      ring

private lemma sub_smul_eq_comp
    {F E : Type}
    [Field F]
    [Field E]
    [Algebra F E]
    [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E)
    (c : E) :
    (σ : E →ₐ[F] E).toLinearMap - c • (LinearMap.id : E →ₗ[F] E) =
      (σ : E →ₐ[F] E).toLinearMap ∘ₗ (1 - T σ c) := by
  ext y
  simp [T_apply, map_mul]

private lemma symm_pow_finrank
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (hσ : orderOf σ = finrank F E)
  : σ.symm ^ finrank F E = 1 := by
  have h : σ.symm = σ⁻¹ := rfl
  rw [h, inv_pow, ← hσ, pow_orderOf_eq_one, inv_one]

private lemma orderOf_symm
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (hσ : orderOf σ = finrank F E)
  : orderOf σ.symm = finrank F E := by
  have h : σ.symm = σ⁻¹ := rfl
  rw [h, orderOf_inv, hσ]

private lemma isGalois
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (hσ : orderOf σ = finrank F E)
  : IsGalois F E := by
  classical
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card]
  refine le_antisymm AlgEquiv.card_le ?_
  rw [← hσ]
  exact orderOf_le_card_univ

private lemma image_pow_range_eq_univ
    {F E : Type}
    [Field F]
    [Field E]
    [Algebra F E]
    [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E)
    (hσ : orderOf σ = finrank F E)
    [DecidableEq (E ≃ₐ[F] E)] :
    (Finset.range (finrank F E)).image (fun i => σ ^ i) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn, Finset.card_range]
  · have := isGalois σ hσ
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa [hσ] using hi) (by simpa [hσ] using hj) hij

private lemma prod_pow_eq_norm
    {F E : Type}
    [Field F]
    [Field E]
    [Algebra F E]
    [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E)
    (hσ : orderOf σ = finrank F E)
    (c : E) :
    ∏ i ∈ Finset.range (finrank F E), (σ ^ i) c = algebraMap F E (Algebra.norm F c) := by
  classical
  have := isGalois σ hσ
  rw [Algebra.norm_eq_prod_automorphisms, ← image_pow_range_eq_univ σ hσ, Finset.prod_image]
  intro i hi j hj hij
  exact pow_injOn_Iio_orderOf (by simpa [hσ] using hi) (by simpa [hσ] using hj) hij

private lemma cf_finrank
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (hσ : orderOf σ = finrank F E)
  (c : E) : cf σ c (finrank F E) = ∏ i ∈ Finset.range (finrank F E), (σ ^ i) c := by
  unfold cf
  rw [← Finset.prod_range_reflect (fun i => (σ ^ i) c) (finrank F E)]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  congr 1
  have h : σ.symm = σ⁻¹ := rfl
  rw [h, inv_pow, inv_eq_iff_mul_eq_one, ← pow_add,
    show j + 1 + (finrank F E - 1 - j) = finrank F E by omega, ← hσ, pow_orderOf_eq_one]

private lemma T_pow_finrank
    {F E : Type}
    [Field F]
    [Field E]
    [Algebra F E]
    [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E)
    (hσ : orderOf σ = finrank F E)
    (c : E) :
    T σ c ^ finrank F E = algebraMap F (Module.End F E) (Algebra.norm F c) := by
  ext y
  rw [T_pow_apply, symm_pow_finrank σ hσ, AlgEquiv.one_apply, cf_finrank σ hσ, prod_pow_eq_norm σ hσ,
    Module.algebraMap_end_apply, Algebra.smul_def]

private lemma eq_zero_of_aeval_eq_zero
    {F E : Type}
    [Field F]
    [Field E]
    [Algebra F E]
    [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E)
    (hσ : orderOf σ = finrank F E)
    {c : E} (hc : c ≠ 0) (p : F[X]) (hp : p.natDegree < finrank F E)
    (hp0 : aeval (T σ c) p = 0) : p = 0 := by
  classical
  set n := finrank F E with hn

  let g : Fin n → (E →* E) := fun i => ((σ.symm ^ (i : ℕ) : E ≃ₐ[F] E) : E →* E)
  have hg : Function.Injective g := by
    intro i j hij
    have h2 : σ.symm ^ (i : ℕ) = σ.symm ^ (j : ℕ) := AlgEquiv.ext fun y => DFunLike.congr_fun hij y
    have h3 := pow_injOn_Iio_orderOf (x := σ.symm)
      (by rw [Set.mem_Iio, orderOf_symm σ hσ]; exact i.2) (by rw [Set.mem_Iio, orderOf_symm σ hσ]; exact j.2) h2
    exact Fin.ext h3
  have hli : LinearIndependent E (fun i : Fin n => (g i : E → E)) :=
    (linearIndependent_monoidHom E E).comp g hg

  have hsum : ∑ i : Fin n, (algebraMap F E (p.coeff i) * cf σ c i) • (g i : E → E) = 0 := by
    funext y
    have h := congrArg (fun f : Module.End F E => f y) hp0
    simp only [LinearMap.zero_apply] at h
    rw [aeval_eq_sum_range' hp, LinearMap.coe_sum, Finset.sum_apply] at h
    rw [Finset.sum_apply, Pi.zero_apply, ← h, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, T_pow_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, mul_assoc]
    rfl
  have hcoef := Fintype.linearIndependent_iff.1 hli _ hsum
  ext i
  rw [coeff_zero]
  by_cases hi : i < n
  · have h := hcoef ⟨i, hi⟩
    rcases mul_eq_zero.1 h with h | h
    · exact (map_eq_zero_iff _ (algebraMap F E).injective).1 h
    · exact absurd h (cf_ne_zero σ hc i)
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp (not_lt.1 hi))

private lemma charpoly_T
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (hσ : orderOf σ = finrank F E)
  (c : E) : (T σ c).charpoly = X ^ finrank F E - C (Algebra.norm F c) := by
  set n := finrank F E with hn
  have hn0 : 0 < n := finrank_pos
  have hPmonic : (X ^ n - C (Algebra.norm F c) : F[X]).Monic := monic_X_pow_sub_C _ hn0.ne'
  have hPdeg : (X ^ n - C (Algebra.norm F c) : F[X]).natDegree = n := natDegree_X_pow_sub_C
  by_cases hc : c = 0
  · subst hc
    have hT : T σ (0 : E) = 0 := by ext y; simp [T_apply]
    rw [hT, LinearMap.charpoly_zero, Algebra.norm_zero, map_zero, sub_zero]

  have haeval : aeval (T σ c) (X ^ n - C (Algebra.norm F c) : F[X]) = 0 := by
    rw [map_sub, aeval_X_pow, aeval_C, T_pow_finrank σ hσ, sub_self]

  have hmin_dvd : minpoly F (T σ c) ∣ X ^ n - C (Algebra.norm F c) := minpoly.dvd F _ haeval
  have hint : IsIntegral F (T σ c) := LinearMap.isIntegral _
  have hmin_deg : n ≤ (minpoly F (T σ c)).natDegree := by
    by_contra h
    have h' : (minpoly F (T σ c)).natDegree < n := not_le.1 h
    exact minpoly.ne_zero hint (eq_zero_of_aeval_eq_zero σ hσ hc _ h' (minpoly.aeval F _))
  have hmin_eq : minpoly F (T σ c) = X ^ n - C (Algebra.norm F c) := by
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPmonic hmin_dvd ?_).symm
    rw [hPdeg]; exact hmin_deg

  have hchar_dvd : minpoly F (T σ c) ∣ (T σ c).charpoly := LinearMap.minpoly_dvd_charpoly _
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (LinearMap.charpoly_monic _) hchar_dvd ?_
    |>.trans hmin_eq
  rw [LinearMap.charpoly_natDegree, hmin_eq, hPdeg]

private lemma det_one_sub_T
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (hσ : orderOf σ = finrank F E)
  (c : E) : LinearMap.det (1 - T σ c) = 1 - Algebra.norm F c := by
  have h := LinearMap.eval_charpoly (T σ c) 1
  rw [charpoly_T σ hσ, map_one] at h
  rw [← h]
  simp

private lemma det_sigma
  {F E : Type}
  [Field F]
  [Field E]
  [Algebra F E]
  [FiniteDimensional F E]
  (σ : E ≃ₐ[F] E)
  (hσ : orderOf σ = finrank F E)
  : LinearMap.det ((σ : E →ₐ[F] E).toLinearMap) = (-1) ^ (finrank F E + 1) := by

  have hT1 : T σ (1 : E) = (σ.symm : E →ₐ[F] E).toLinearMap := by ext y; simp [T_apply]
  have hdet_symm : LinearMap.det ((σ.symm : E →ₐ[F] E).toLinearMap) = (-1) ^ (finrank F E + 1) := by
    rw [← hT1, LinearMap.det_eq_sign_charpoly_coeff, charpoly_T σ hσ, map_one]
    have hn0 : 0 < finrank F E := finrank_pos
    rw [coeff_sub, coeff_X_pow, coeff_C_zero, ite_eq_right hn0.ne, zero_sub, pow_succ, mul_neg_one]
  have hprod : LinearMap.det ((σ : E →ₐ[F] E).toLinearMap) *
      LinearMap.det ((σ.symm : E →ₐ[F] E).toLinearMap) = 1 := by
    rw [← LinearMap.det_comp]
    have : (σ : E →ₐ[F] E).toLinearMap ∘ₗ (σ.symm : E →ₐ[F] E).toLinearMap = LinearMap.id := by
      ext y; simp
    rw [this, LinearMap.det_id]
  rw [hdet_symm] at hprod
  have hu : ((-1 : F) ^ (finrank F E + 1)) * (-1) ^ (finrank F E + 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc LinearMap.det ((σ : E →ₐ[F] E).toLinearMap)
      = LinearMap.det ((σ : E →ₐ[F] E).toLinearMap) * ((-1) ^ (finrank F E + 1) * (-1) ^ (finrank F E + 1)) := by
        rw [hu, mul_one]
    _ = (-1) ^ (finrank F E + 1) := by rw [← mul_assoc, hprod, one_mul]

private lemma det_sub_smul_eq
    {F E : Type}
    [Field F]
    [Field E]
    [Algebra F E]
    [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E)
    (hσ : orderOf σ = finrank F E)
    (c : E) :
    algebraMap F E (LinearMap.det ((σ : E →ₐ[F] E).toLinearMap - c • (LinearMap.id : E →ₗ[F] E))) =
      (-1) ^ (finrank F E - 1) * (1 - ∏ i ∈ Finset.range (finrank F E), (σ ^ i) c) := by
  rw [sub_smul_eq_comp, LinearMap.det_comp, det_sigma σ hσ, det_one_sub_T σ hσ, prod_pow_eq_norm σ hσ,
    map_mul, map_pow, map_neg, map_one, map_sub, map_one]
  have hn0 : 0 < finrank F E := finrank_pos
  congr 1
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hn0
  rw [hk, zero_add, Nat.add_sub_cancel, pow_succ, pow_succ, mul_assoc, neg_one_mul, neg_neg, mul_one]
@[path]
private lemma main
  {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {c : E}
-- given
  (σ : E ≃ₐ[F] E)
  (hσ : orderOf σ = Module.finrank F E) :
-- imply
  algebraMap F E (LinearMap.det ((σ : E →ₐ[F] E).toLinearMap - c • (LinearMap.id : E →ₗ[F] E))) =
      (-1) ^ (Module.finrank F E - 1) *
        (1 - ∏ i ∈ Finset.range (Module.finrank F E), (σ ^ i) c) :=
-- proof
  det_sub_smul_eq σ hσ c


-- created on 2026-10-09
