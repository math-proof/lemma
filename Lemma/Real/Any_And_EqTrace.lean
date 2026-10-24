import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma p_pos (p : ℕ) [Fact p.Prime] : (0 : ℝ) < p := by
  exact_mod_cast (Fact.out : p.Prime).pos

private lemma one_lt_p (p : ℕ) [Fact p.Prime] : (1 : ℝ) < p := by
  exact_mod_cast (Fact.out : p.Prime).one_lt

private lemma norm_natCast_p (p : ℕ) [Fact p.Prime] : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap', Padic.norm_p]

private lemma exists_norm_eq_rpow_of_natDegree_le (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) {d : ℕ} (hd : (minpoly ℚ_[p] x).natDegree ≤ d) : ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ ((k : ℝ) / (d.factorial : ℝ)) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  set m := (minpoly ℚ_[p] x).natDegree
  have hmpos : 0 < m := minpoly.natDegree_pos hint
  have hc0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have hnorm : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (m : ℝ)) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := PadicAlgCl p) x
  rw [Padic.norm_eq_zpow_neg_valuation hc0] at hnorm
  set v : ℤ := ((minpoly ℚ_[p] x).coeff 0).valuation
  have hmd : m ∣ d.factorial := Nat.dvd_factorial hmpos hd
  obtain ⟨q, hq⟩ := hmd
  refine ⟨-v * q, ?_⟩
  rw [hnorm, ← Real.rpow_intCast, ← Real.rpow_mul (p_pos p).le]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hq0 : (q : ℝ) ≠ 0 := by
    intro hq0
    have : (q : ℕ) = 0 := by exact_mod_cast hq0
    rw [this, mul_zero] at hq
    exact (Nat.factorial_pos d).ne' hq
  have hdf : (d.factorial : ℝ) = (m : ℝ) * (q : ℝ) := by exact_mod_cast hq
  rw [hdf]
  field_simp
  push_cast
  ring

private lemma exists_norm_coe_eq_rpow (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F] {x : F} (hx : x ≠ 0) : ∃ k : ℤ, ‖(x : PadicAlgCl p)‖ = (p : ℝ) ^ ((k : ℝ) / ((Module.finrank ℚ_[p] F).factorial : ℝ)) := by
  have hx' : (x : PadicAlgCl p) ≠ 0 := by
    simpa using hx
  refine exists_norm_eq_rpow_of_natDegree_le p hx' ?_
  have h1 : minpoly ℚ_[p] (x : PadicAlgCl p) = minpoly ℚ_[p] x := minpoly.algebraMap_eq (algebraMap F (PadicAlgCl p)).injective x
  rw [h1]
  refine minpoly.natDegree_le x

private lemma norm_algHom_apply (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (E : IntermediateField F (PadicAlgCl p)) (σ : E →ₐ[F] PadicAlgCl p) (y : E) : ‖σ y‖ = ‖(y : PadicAlgCl p)‖ := by
  have h1 : minpoly ℚ_[p] (σ y) = minpoly ℚ_[p] y := minpoly.algHom_eq (σ.restrictScalars ℚ_[p]) σ.injective y
  have h2 : minpoly ℚ_[p] (E.val y) = minpoly ℚ_[p] y := minpoly.algHom_eq (E.val.restrictScalars ℚ_[p]) (algebraMap E (PadicAlgCl p)).injective y
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, h1]
  change spectralValue (minpoly ℚ_[p] y) = spectralValue (minpoly ℚ_[p] (E.val y))
  rw [h2]

private lemma norm_trace_le (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] (y : E) : ‖((Algebra.trace F E y : F) : PadicAlgCl p)‖ ≤ ‖(y : PadicAlgCl p)‖ := by
  let _ : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have h := trace_eq_sum_embeddings (PadicAlgCl p) (K := F) (L := E) (x := y)
  have h' : ((Algebra.trace F E y : F) : PadicAlgCl p) = ∑ σ : E →ₐ[F] PadicAlgCl p, σ y := h
  rw [h']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
  intro σ _
  exact (norm_algHom_apply p F E σ y).le

private lemma norm_trace_le_one (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] {y : E} (hy : ‖(y : PadicAlgCl p)‖ ≤ 1) : ‖((Algebra.trace F E y : F) : PadicAlgCl p)‖ ≤ 1 := (norm_trace_le p F E y).trans hy

private lemma exists_trace_ne_zero (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F] (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] : ∃ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F E y ≠ 0 := by
  let _ : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  obtain ⟨y, hy⟩ : ∃ y : E, Algebra.trace F E y ≠ 0 := by
    by_contra h
    push Not at h
    exact Algebra.trace_ne_zero F E (LinearMap.ext h)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(y : PadicAlgCl p)‖ ≤ (p : ℝ) ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖(y : PadicAlgCl p)‖ (one_lt_p p)
    exact ⟨N, hN.le⟩
  refine ⟨algebraMap ℚ_[p] E ((p : ℚ_[p]) ^ N) * y, ?_, ?_⟩
  ·
    have hcoe : ((algebraMap ℚ_[p] E ((p : ℚ_[p]) ^ N) * y : E) : PadicAlgCl p) = (p : PadicAlgCl p) ^ N * (y : PadicAlgCl p) := by
      push_cast
      congr 1
    rw [hcoe, norm_mul, norm_pow, norm_natCast_p, inv_pow]
    have hpN : (0 : ℝ) < (p : ℝ) ^ N := pow_pos (p_pos p) N
    calc
      _ ≤ ((p : ℝ) ^ N)⁻¹ * (p : ℝ) ^ N := by gcongr
      _ = 1 := inv_mul_cancel₀ hpN.ne'
  ·
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.map_smul_of_tower]
    refine smul_ne_zero ?_ hy
    exact pow_ne_zero N (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

private noncomputable def expo (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F] (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] (k : ℤ) : Prop :=
  ∃ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F E y ≠ 0 ∧ ‖((Algebra.trace F E y : F) : PadicAlgCl p)‖ = (p : ℝ) ^ ((k : ℝ) / ((Module.finrank ℚ_[p] F).factorial : ℝ))

private lemma expo_le_zero (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F] (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] {k : ℤ} (hk : expo p F E k) : k ≤ 0 := by
  obtain ⟨y, hy, -, hk⟩ := hk
  have h1 : ‖((Algebra.trace F E y : F) : PadicAlgCl p)‖ ≤ 1 := norm_trace_le_one p F E hy
  rw [hk] at h1
  have hD : (0 : ℝ) < ((Module.finrank ℚ_[p] F).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h2 : (k : ℝ) / ((Module.finrank ℚ_[p] F).factorial : ℝ) ≤ 0 := by
    by_contra h3
    push Not at h3
    have := Real.one_lt_rpow (one_lt_p p) h3
    linarith
  have h3 : (k : ℝ) ≤ 0 := by
    by_contra h4
    push Not at h4
    exact absurd (div_pos h4 hD) (not_lt.mpr h2)
  exact_mod_cast h3

private lemma exists_max_trace (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F] (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] : ∃ y₀ : E, ‖(y₀ : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F E y₀ ≠ 0 ∧ ∀ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 → ‖((Algebra.trace F E y : F) : PadicAlgCl p)‖ ≤ ‖((Algebra.trace F E y₀ : F) : PadicAlgCl p)‖ := by
  have hinh : ∃ k : ℤ, expo p F E k := by
    obtain ⟨y, hy, hty⟩ := exists_trace_ne_zero p F E
    obtain ⟨k, hk⟩ := exists_norm_coe_eq_rpow p F hty
    exact ⟨k, y, hy, hty, hk⟩
  obtain ⟨k₀, ⟨y₀, hy₀, hty₀, hk₀⟩, hmax⟩ := Int.exists_greatest_of_bdd ⟨0, fun k hk => expo_le_zero p F E hk⟩ hinh
  refine ⟨y₀, hy₀, hty₀, fun y hy => ?_⟩
  if hty : Algebra.trace F E y = 0 then
    rw [hty]
    simp
  else
    obtain ⟨k, hk⟩ := exists_norm_coe_eq_rpow p F hty
    have hkk : k ≤ k₀ := hmax k ⟨y, hy, hty, hk⟩
    rw [hk, hk₀]
    refine Real.rpow_le_rpow_of_exponent_le (one_lt_p p).le ?_
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkk) (by exact_mod_cast (Nat.factorial_pos _).le)

private lemma helper_main (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F] (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] (r : ℝ) (hE : ∀ z : E, (∀ w : E, ‖(w : PadicAlgCl p)‖ ≤ 1 → ‖((Algebra.trace F E (z * w) : F) : PadicAlgCl p)‖ ≤ 1) → ‖(z : PadicAlgCl p)‖ ≤ r) (x : F) (hx : ‖(x : PadicAlgCl p)‖ ≤ r⁻¹) : ∃ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F E y = x := by
  obtain ⟨y₀, hy₀, hty₀, hmax⟩ := exists_max_trace p F E
  set t₀ : F := Algebra.trace F E y₀ with ht₀
  have ht₀' : (t₀ : PadicAlgCl p) ≠ 0 := by simpa using hty₀
  have hnt₀ : 0 < ‖(t₀ : PadicAlgCl p)‖ := norm_pos_iff.mpr ht₀'
  have hz : ‖((algebraMap F E t₀⁻¹ : E) : PadicAlgCl p)‖ ≤ r := by
    refine hE _ fun w hw => ?_
    have h1 : Algebra.trace F E (algebraMap F E t₀⁻¹ * w) = t₀⁻¹ * Algebra.trace F E w := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
    rw [h1]
    push_cast
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hnt₀, mul_one]
    exact hmax w hw
  have hzr : ‖(t₀ : PadicAlgCl p)‖⁻¹ ≤ r := by
    have : ((algebraMap F E t₀⁻¹ : E) : PadicAlgCl p) = (t₀ : PadicAlgCl p)⁻¹ := by
      rw [IntermediateField.coe_algebraMap_apply]
      push_cast
      rfl
    rwa [this, norm_inv] at hz
  have hr : 0 < r := lt_of_lt_of_le (inv_pos.mpr hnt₀) hzr
  have hxt : ‖(x : PadicAlgCl p)‖ ≤ ‖(t₀ : PadicAlgCl p)‖ := by
    refine hx.trans ?_
    rwa [inv_le_comm₀ hr hnt₀]
  refine ⟨algebraMap F E (x * t₀⁻¹) * y₀, ?_, ?_⟩
  ·
    have hcoe : ((algebraMap F E (x * t₀⁻¹) * y₀ : E) : PadicAlgCl p) = (x : PadicAlgCl p) * (t₀ : PadicAlgCl p)⁻¹ * (y₀ : PadicAlgCl p) := by
      push_cast
      rfl
    rw [hcoe, norm_mul, norm_mul, norm_inv]
    have h1 : ‖(x : PadicAlgCl p)‖ * ‖(t₀ : PadicAlgCl p)‖⁻¹ ≤ 1 := by
      rwa [mul_inv_le_iff₀ hnt₀, one_mul]
    have hle : ‖(x : PadicAlgCl p)‖ * ‖(t₀ : PadicAlgCl p)‖⁻¹ * ‖(y₀ : PadicAlgCl p)‖ ≤ 1 := calc
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
    refine hle
  ·
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul, ← ht₀, mul_assoc, inv_mul_cancel₀ hty₀, mul_one]

/--
[PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime]
  (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
  (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E]
  (r : ℝ)
  (hE : ∀ z : E, (∀ w : E, ‖(w : PadicAlgCl p)‖ ≤ 1 → ‖((Algebra.trace F E (z * w) : F) : PadicAlgCl p)‖ ≤ 1) → ‖(z : PadicAlgCl p)‖ ≤ r)
  (x : F)
  (hx : ‖(x : PadicAlgCl p)‖ ≤ r⁻¹) :
  -- imply
  ∃ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F E y = x :=
    helper_main p F E r hE x hx


-- created on 2026-10-20
