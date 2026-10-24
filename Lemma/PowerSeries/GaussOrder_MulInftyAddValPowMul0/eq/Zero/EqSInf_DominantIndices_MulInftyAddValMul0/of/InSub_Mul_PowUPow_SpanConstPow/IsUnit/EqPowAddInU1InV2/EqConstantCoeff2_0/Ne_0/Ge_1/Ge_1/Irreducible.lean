import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_UVCrossingModel
import Lemma.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Lemma.Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Lemma.Int.P2MUtil

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

/--
[ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem.lean)
-/

private lemma  coeff_X_mul_X_mul_single
  {W : Type*}
  [CommRing W]
  (G : MvPowerSeries (Fin 2) W) (s : Fin 2) (j : ℕ) :
  MvPowerSeries.coeff (Finsupp.single s j)
    ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 * G) = 0 := by
  classical
  have hXX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 =
      MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [hXX, MvPowerSeries.coeff_monomial_mul, ite_eq_right]
  intro h
  fin_cases s
  ·
    have := h 1
    simp at this
  ·
    have := h 0
    simp at this

private lemma  coeff_axis_of_congr
  {W : Type*}
  [CommRing W]
  (π ϖ : W) (e : ℕ) (he : 1 ≤ e) (hπ : π = ϖ ^ e) (s s' : Fin 2) (hss' : s ≠ s')
  (F G : MvPowerSeries (Fin 2) W) (n : ℕ)
  (h : mk π F - mk π G * mk π (MvPowerSeries.X s) ^ n ∈
    Ideal.span {mk π (MvPowerSeries.C ϖ), mk π (MvPowerSeries.X s')}) (j : ℕ) :
  ∃ z : W, MvPowerSeries.coeff (Finsupp.single s j) F =
    (if n ≤ j then MvPowerSeries.coeff (Finsupp.single s (j - n)) G else 0) + ϖ * z := by
  classical
  obtain ⟨r, t, hrt⟩ := Ideal.mem_span_pair.mp h
  obtain ⟨Rr, rfl⟩ := mk_surjective π r
  obtain ⟨T, rfl⟩ := mk_surjective π t
  have hmem : F - G * MvPowerSeries.X s ^ n - (Rr * MvPowerSeries.C ϖ + T * MvPowerSeries.X s') ∈
    uvCrossingIdeal W π := by
    rw [← Ideal.Quotient.eq]
    change mk π _ = mk π _
    rw [map_sub, map_mul, map_pow, map_add, map_mul, map_mul, hrt]
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single s j)) hQ
  rw [mul_comm, sub_mul, map_sub, coeff_X_mul_X_mul_single, MvPowerSeries.coeff_C_mul, zero_sub,
    map_sub, map_sub, map_add, MvPowerSeries.coeff_mul_C, MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_mul_monomial, MvPowerSeries.X, MvPowerSeries.coeff_mul_monomial] at hc
  have hle : Finsupp.single s n ≤ Finsupp.single s j ↔ n ≤ j := by
    constructor
    ·
      intro h'
      simpa using h' s
    ·
      intro h' i
      by_cases hi : s = i
      ·
        subst hi
        simpa using h'
      · simp [hi]
  have hsub : Finsupp.single s j - Finsupp.single s n = Finsupp.single s (j - n) := by
    ext i
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> simp
  have hle' : ¬ Finsupp.single s' 1 ≤ Finsupp.single s j := by
    intro h'
    have := h' s'
    simp [hss'] at this
  rw [ite_eq_right hle', add_zero, hsub, mul_one] at hc
  simp only [hle] at hc
  have hπ' : π = ϖ * ϖ ^ (e - 1) := by rw [hπ, ← pow_succ', Nat.sub_add_cancel he]
  rw [hπ'] at hc
  exact ⟨MvPowerSeries.coeff (Finsupp.single s j) Rr - ϖ ^ (e - 1) * MvPowerSeries.coeff (Finsupp.single s j) Q,
    by linear_combination -hc⟩

private lemma  constantCoeff_mul_eq_of_isUnit_mk
  {W : Type*}
  [CommRing W]
  (π : W) (G : MvPowerSeries (Fin 2) W) (hG : IsUnit (mk π G)) :
  ∃ D Q : MvPowerSeries (Fin 2) W,
    MvPowerSeries.constantCoeff G * MvPowerSeries.constantCoeff D = 1 - π * MvPowerSeries.constantCoeff Q := by
  obtain ⟨δ, hδ⟩ := hG.exists_right_inv
  obtain ⟨D, rfl⟩ := mk_surjective π δ
  have hmem : G * D - 1 ∈ uvCrossingIdeal W π := by
    rw [← Ideal.Quotient.eq]
    change mk π _ = mk π _
    rw [map_mul, map_one, hδ]
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  have hc := congrArg MvPowerSeries.constantCoeff hQ
  simp only [map_mul, map_sub, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C,
    mul_zero, zero_sub] at hc
  exact ⟨D, Q, by linear_combination -hc⟩

private lemma  one_le_addVal_of_eq_mul
  {W : Type*}
  [CommRing W]
  [IsDomain W]
  [IsDiscreteValuationRing W]
  {ϖ : W} (hϖ : Irreducible ϖ) {c z : W} (h : c = ϖ * z) :
  1 ≤ IsDiscreteValuationRing.addVal W c := by
  rw [h, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  exact le_self_add

private lemma  addVal_eq_zero_of_isUnit
  {W : Type*}
  [CommRing W]
  [IsDomain W]
  [IsDiscreteValuationRing W]
  {ϖ : W} (hϖ : Irreducible ϖ) {c : W} (hc : IsUnit c) :
  IsDiscreteValuationRing.addVal W c = 0 := by
  obtain ⟨u, rfl⟩ := hc
  have := IsDiscreteValuationRing.addVal_def (u : W) u hϖ 0 (by simp)
  simpa using this

private lemma  isUnit_add_mul
  {W : Type*}
  [CommRing W]
  [IsDomain W]
  [IsDiscreteValuationRing W]
  {ϖ : W} (hϖ : Irreducible ϖ) {g z : W} (hg : IsUnit g) : IsUnit (g + ϖ * z) := by
  by_contra h
  have h1 : g + ϖ * z ∈ maximalIdeal W := (mem_maximalIdeal _).mpr h
  have h2 : ϖ * z ∈ maximalIdeal W := Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr hϖ.not_isUnit)
  have h3 : g ∈ maximalIdeal W := by simpa using sub_mem h1 h2
  refine (mem_maximalIdeal _).mp h3 hg

private lemma  isUnit_constantCoeff_of_isUnit_mk
  {W : Type*}
  [CommRing W]
  [IsDomain W]
  [IsDiscreteValuationRing W]
  {ϖ : W} (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
  (G : MvPowerSeries (Fin 2) W) (hG : IsUnit (mk (ϖ ^ e) G)) : IsUnit (MvPowerSeries.constantCoeff G) := by
  obtain ⟨D, Q, hGD⟩ := constantCoeff_mul_eq_of_isUnit_mk (ϖ ^ e) G hG
  have hu : IsUnit (1 - ϖ ^ e * MvPowerSeries.constantCoeff Q) := by
    apply isUnit_one_sub_self_of_mem_nonunits
    rw [← Nat.sub_add_cancel he, pow_succ', mul_assoc]
    exact mul_mem_nonunits_left hϖ.not_isUnit
  rw [← hGD] at hu
  exact isUnit_of_mul_isUnit_left hu

private lemma  addVal_coeff_axis
  {W : Type*}
  [CommRing W]
  [IsDomain W]
  [IsDiscreteValuationRing W]
  {ϖ : W} (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (s s' : Fin 2) (hss' : s ≠ s')
  (F G : MvPowerSeries (Fin 2) W) (hG : IsUnit (mk (ϖ ^ e) G)) (n : ℕ)
  (h : mk (ϖ ^ e) F - mk (ϖ ^ e) G * mk (ϖ ^ e) (MvPowerSeries.X s) ^ n ∈
    Ideal.span {mk (ϖ ^ e) (MvPowerSeries.C ϖ), mk (ϖ ^ e) (MvPowerSeries.X s')}) :
  (∀ j, j < n → 1 ≤ IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff (Finsupp.single s j) F)) ∧
    IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff (Finsupp.single s n) F) = 0 := by
  constructor
  ·
    intro j hj
    obtain ⟨z, hz⟩ := coeff_axis_of_congr (ϖ ^ e) ϖ e he rfl s s' hss' F G n h j
    rw [ite_eq_right (by omega), zero_add] at hz
    exact one_le_addVal_of_eq_mul hϖ hz
  ·
    obtain ⟨z, hz⟩ := coeff_axis_of_congr (ϖ ^ e) ϖ e he rfl s s' hss' F G n h n
    rw [ite_eq_left le_rfl, Nat.sub_self, Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hz
    rw [hz]
    exact addVal_eq_zero_of_isUnit hϖ (isUnit_add_mul hϖ (isUnit_constantCoeff_of_isUnit_mk hϖ e he G hG))

private lemma  sSup_dominantIndices_eq_neg
  {W : Type*}
  [CommRing W]
  [IsDomain W]
  [IsDiscreteValuationRing W]
  [IsAdicComplete (maximalIdeal W) W]
  (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
  (x : UVCrossingModel W (ϖ ^ e))
  (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
  (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
  (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (n : ℕ)
  (hxγ : x - γ * V (ϖ ^ e) ^ n ∈ Ideal.span {const (ϖ ^ e) ϖ, U (ϖ ^ e)}) :
  gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e) x = 0 ∧
    sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab) = -(n : ℤ) := by
  classical
  obtain ⟨G, rfl⟩ := mk_surjective (ϖ ^ e) γ
  have key : ∀ F : MvPowerSeries (Fin 2) W, mk (ϖ ^ e) F = x →
      (∀ j, j < n → 1 ≤ IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff (Finsupp.single 1 j) F)) ∧
        IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff (Finsupp.single 1 n) F) = 0 := by
    intro F hF
    apply addVal_coeff_axis hϖ e he 1 0 (by decide) F G hγ n
    rwa [hF]
  set vq : W → ℕ∞ := fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w with hvq
  have hw : ∀ j, annulusWeight (q * e) (q * e) (Finsupp.single (1 : Fin 2) j) = 0 := by
    intro j; simp [annulusWeight]
  have hrep0 : ∀ F : MvPowerSeries (Fin 2) W, mk (ϖ ^ e) F = x → repGaussOrder vq (q * e) (q * e) F ≤ 0 := by
    intro F hF
    refine le_trans (repGaussOrder_le vq _ _ F (Finsupp.single 1 n)) ?_
    rw [hw]
    simp only [hvq]
    rw [(key F hF).2]
    simp
  refine ⟨le_antisymm ((gaussOrder_le_iff vq _ _ _ x 0).mpr hrep0) zero_le, ?_⟩
  have hrep : repGaussOrder vq (q * e) (q * e) (inU ab.1 + inV ab.2) = 0 :=
    le_antisymm (hrep0 _ habx) zero_le
  obtain ⟨hlow, htop⟩ := key _ habx
  have hb' : PowerSeries.coeff 0 ab.2 = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hb
  have hcoef0 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 0) (inU ab.1 + inV ab.2) =
      PowerSeries.coeff 0 ab.1 := by
    rw [map_add, coeff_inU, coeff_inV]; simp [hb']
  have hcoefS : ∀ j : ℕ, MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) (j + 1)) (inU ab.1 + inV ab.2) =
      PowerSeries.coeff (j + 1) ab.2 := by
    intro j; rw [map_add, coeff_inU, coeff_inV]; simp
  have hq0 : (q : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hT0 : ∀ i : ℕ, termOrder vq (q * e) (q * e) ab (Int.ofNat i) =
      (q : ℕ∞) * IsDiscreteValuationRing.addVal W (PowerSeries.coeff i ab.1) + ((i * (q * e) : ℕ) : ℕ∞) := by
    intro i
    show (q : ℕ∞) * IsDiscreteValuationRing.addVal W (PowerSeries.coeff i ab.1) +
      ((annulusWeight (q * e) (q * e) (Finsupp.single 0 i) : ℕ) : ℕ∞) = _
    simp [annulusWeight]
  have hT1 : ∀ j : ℕ, termOrder vq (q * e) (q * e) ab (Int.negSucc j) =
      (q : ℕ∞) * IsDiscreteValuationRing.addVal W (PowerSeries.coeff (j + 1) ab.2) := by
    intro j
    show (q : ℕ∞) * IsDiscreteValuationRing.addVal W (PowerSeries.coeff (j + 1) ab.2) +
      ((annulusWeight (q * e) (q * e) (Finsupp.single 1 (j + 1)) : ℕ) : ℕ∞) = _
    simp [annulusWeight]
  apply IsGreatest.csSup_eq
  constructor
  ·
    show termOrder vq (q * e) (q * e) ab (-(n : ℤ)) = repGaussOrder vq (q * e) (q * e) (inU ab.1 + inV ab.2)
    rw [hrep]
    cases n with
    | zero =>
        show termOrder vq (q * e) (q * e) ab (Int.ofNat 0) = 0
        rw [hT0, ← hcoef0, htop]; simp
    | succ k =>
        show termOrder vq (q * e) (q * e) ab (Int.negSucc k) = 0
        rw [hT1, ← hcoefS, htop]; simp
  ·
    intro N hN
    change termOrder vq (q * e) (q * e) ab N = repGaussOrder vq (q * e) (q * e) (inU ab.1 + inV ab.2) at hN
    rw [hrep] at hN
    cases N with
    | ofNat i =>
        rw [hT0, add_eq_zero] at hN
        obtain ⟨h1, h2⟩ := hN
        rw [mul_eq_zero] at h1
        rw [Nat.cast_eq_zero] at h2
        have hi : i = 0 := by
          rcases Nat.mul_eq_zero.mp h2 with h3 | h3
          · exact h3
          ·
            exfalso
            rcases Nat.mul_eq_zero.mp h3 with h4 | h4 <;> omega
        subst hi
        have ha0 : IsDiscreteValuationRing.addVal W (PowerSeries.coeff 0 ab.1) = 0 := by
          rcases h1 with h1 | h1
          · exact absurd h1 hq0
          · exact h1
        rcases Nat.eq_zero_or_pos n with hn | hn
        ·
          subst hn
          simp
        ·
          exfalso
          have := hlow 0 hn
          rw [hcoef0, ha0] at this
          simp at this
    | negSucc j =>
        rw [hT1, mul_eq_zero] at hN
        have hbj : IsDiscreteValuationRing.addVal W (PowerSeries.coeff (j + 1) ab.2) = 0 := by
          rcases hN with h1 | h1
          · exact absurd h1 hq0
          · exact h1
        have hnj : n ≤ j + 1 := by
          by_contra hlt
          push Not at hlt
          have := hlow (j + 1) hlt
          rw [hcoefS, hbj] at this
          simp at this
        rw [Int.negSucc_eq]; omega

private lemma  sInf_dominantIndices_eq
  {W : Type*}
  [CommRing W]
  [IsDomain W]
  [IsDiscreteValuationRing W]
  [IsAdicComplete (maximalIdeal W) W]
  (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
  (x : UVCrossingModel W (ϖ ^ e))
  (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
  (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
  (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (m : ℕ)
  (hxγ : x - γ * U (ϖ ^ e) ^ m ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)}) :
  gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x = 0 ∧
    sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab) = (m : ℤ) := by
  classical
  obtain ⟨G, rfl⟩ := mk_surjective (ϖ ^ e) γ
  have key : ∀ F : MvPowerSeries (Fin 2) W, mk (ϖ ^ e) F = x →
      (∀ i, i < m → 1 ≤ IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff (Finsupp.single 0 i) F)) ∧
        IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff (Finsupp.single 0 m) F) = 0 := by
    intro F hF
    apply addVal_coeff_axis hϖ e he 0 1 (by decide) F G hγ m
    rwa [hF]
  set vq : W → ℕ∞ := fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w with hvq
  have hw : ∀ i, annulusWeight (q * e) 0 (Finsupp.single (0 : Fin 2) i) = 0 := by
    intro i; simp [annulusWeight]
  have hrep0 : ∀ F : MvPowerSeries (Fin 2) W, mk (ϖ ^ e) F = x → repGaussOrder vq (q * e) 0 F ≤ 0 := by
    intro F hF
    refine le_trans (repGaussOrder_le vq _ _ F (Finsupp.single 0 m)) ?_
    rw [hw]
    simp only [hvq]
    rw [(key F hF).2]
    simp
  refine ⟨le_antisymm ((gaussOrder_le_iff vq _ _ _ x 0).mpr hrep0) zero_le, ?_⟩
  have hrep : repGaussOrder vq (q * e) 0 (inU ab.1 + inV ab.2) = 0 :=
    le_antisymm (hrep0 _ habx) zero_le
  obtain ⟨hlow, htop⟩ := key _ habx
  have hb' : PowerSeries.coeff 0 ab.2 = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hb
  have hcoef : ∀ i : ℕ, MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i) (inU ab.1 + inV ab.2) =
      PowerSeries.coeff i ab.1 := by
    intro i
    rw [map_add, coeff_inU, coeff_inV]
    by_cases hi : i = 0
    ·
      subst hi
      simp [hb']
    · simp [hi]
  have hq0 : (q : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqe : 0 < q * e := Nat.mul_pos (by omega) (by omega)
  have hT0 : ∀ i : ℕ, termOrder vq (q * e) 0 ab (Int.ofNat i) =
      (q : ℕ∞) * IsDiscreteValuationRing.addVal W (PowerSeries.coeff i ab.1) := by
    intro i
    show (q : ℕ∞) * IsDiscreteValuationRing.addVal W (PowerSeries.coeff i ab.1) +
      ((annulusWeight (q * e) 0 (Finsupp.single 0 i) : ℕ) : ℕ∞) = _
    simp [annulusWeight]
  have hT1 : ∀ j : ℕ, termOrder vq (q * e) 0 ab (Int.negSucc j) =
      (q : ℕ∞) * IsDiscreteValuationRing.addVal W (PowerSeries.coeff (j + 1) ab.2) +
        (((j + 1) * (q * e) : ℕ) : ℕ∞) := by
    intro j
    show (q : ℕ∞) * IsDiscreteValuationRing.addVal W (PowerSeries.coeff (j + 1) ab.2) +
      ((annulusWeight (q * e) 0 (Finsupp.single 1 (j + 1)) : ℕ) : ℕ∞) = _
    simp [annulusWeight]
  apply IsLeast.csInf_eq
  constructor
  ·
    show termOrder vq (q * e) 0 ab (Int.ofNat m) = repGaussOrder vq (q * e) 0 (inU ab.1 + inV ab.2)
    rw [hrep, hT0, ← hcoef, htop]; simp
  ·
    intro N hN
    change termOrder vq (q * e) 0 ab N = repGaussOrder vq (q * e) 0 (inU ab.1 + inV ab.2) at hN
    rw [hrep] at hN
    cases N with
    | ofNat i =>
        rw [hT0, mul_eq_zero] at hN
        have hai : IsDiscreteValuationRing.addVal W (PowerSeries.coeff i ab.1) = 0 := by
          rcases hN with h1 | h1
          · exact absurd h1 hq0
          · exact h1
        have hmi : m ≤ i := by
          by_contra hlt
          push Not at hlt
          have := hlow i hlt
          rw [hcoef, hai] at this
          simp at this
        show ((i : ℕ) : ℤ) ≥ m
        omega
    | negSucc j =>
        exfalso
        rw [hT1, add_eq_zero] at hN
        obtain ⟨-, h2⟩ := hN
        rw [Nat.cast_eq_zero] at h2
        rcases Nat.mul_eq_zero.mp h2 with h3 | h3
        · omega
        · rcases Nat.mul_eq_zero.mp h3 with h4 | h4 <;> omega


open in
@[path]
private lemma main
  {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  {ϖ : W}
  {e : ℕ}
  {q : ℕ}
  {x : UVCrossingModel W (ϖ ^ e)}
  {ab : PowerSeries W × PowerSeries W}
  {γ : UVCrossingModel W (ϖ ^ e)}
  {m : ℕ}
-- given
  (hϖ : Irreducible ϖ)
  (he : 1 ≤ e)
  (hq : 1 ≤ q)
  (hx : x ≠ 0)
  (hb : PowerSeries.constantCoeff ab.2 = 0)
  (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
  (hγ : IsUnit γ)
  (hxγ : x - γ * U (ϖ ^ e) ^ m ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)}) :
-- imply
  gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x = 0 ∧
      sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab) = (m : ℤ) :=
-- proof
  sInf_dominantIndices_eq ϖ hϖ e he q hq x ab hb habx γ hγ m hxγ


-- created on 2026-10-23
