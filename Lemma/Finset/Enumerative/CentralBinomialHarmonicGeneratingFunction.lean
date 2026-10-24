import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[choose_succ_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma choose_succ_mul (a : ℝ) (n : ℕ) :
  ((n : ℝ) + 1) * Ring.choose a (n + 1) = (a - n) * Ring.choose a n := by
  have h1 := Ring.choose_eq_smul (R := ℝ) (a := a) (n := n + 1)
  have h0 := Ring.choose_eq_smul (R := ℝ) (a := a) (n := n)
  have hD := descPochhammer_succ_right ℤ n
  have hfact : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hP : (descPochhammer ℤ (n + 1)).smeval a
    = (descPochhammer ℤ n).smeval a * (a - n) := by
    rw [hD, Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      Polynomial.smeval_natCast]
    simp [pow_zero, pow_one]
  have hfact_ne : ((n.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hn1_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [h1, h0, hP, hfact]
  simp only [smul_eq_mul]
  field_simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[choose_neg_half_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma choose_neg_half_mul (n : ℕ) :
  Ring.choose (-1/2 : ℝ) n * (-4) ^ n = (Nat.centralBinom n : ℝ) := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ n ih =>
    have hrec := choose_succ_mul (-1/2 : ℝ) n
    have hcb := Nat.succ_mul_centralBinom_succ n
    have hn1_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hcbR : ((n : ℝ) + 1) * ((Nat.centralBinom (n + 1) : ℕ) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * ((Nat.centralBinom n : ℕ) : ℝ) := by
      have := congrArg (Nat.cast (R := ℝ)) hcb
      push_cast at this ⊢
      linarith [this]
    have hfactor : ((-1/2 : ℝ) - (n : ℝ)) * (-4) = 2 * (2 * (n : ℝ) + 1) := by ring
    have hstep : Ring.choose (-1/2 : ℝ) (n + 1) * (-4) ^ (n + 1)
      = (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1))
        * (Ring.choose (-1/2 : ℝ) n * (-4) ^ n) := by
      rw [pow_succ]
      field_simp
      nlinarith [hrec, hfactor]
    rw [hstep, ih]
    field_simp
    linarith [hcbR]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialSeries_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma binomialSeries_coeff (a z : ℝ) (n : ℕ) :
  ((binomialSeries ℝ a n) fun _ => z) = Ring.choose a n * z ^ n := by
  rw [binomialSeries_apply]
  simp [List.ofFn_const, List.prod_replicate, smul_eq_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hasSum_centralBinom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma hasSum_centralBinom (y : ℝ) (hy : |y| < 1 / 4) :
  HasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) * y ^ n)
    (1 / Real.sqrt (1 - 4 * y)) := by
  have hz : |(-4 : ℝ) * y| < 1 := by
    have h : |(-4 : ℝ) * y| = 4 * |y| := by rw [abs_mul]; norm_num
    rw [h]; linarith
  have hmem : (-4 * y) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right, Real.norm_eq_abs,
      ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    exact hz
  have hbase := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1/2 : ℝ))).hasSum_sub hmem
  simp only [sub_zero] at hbase
  have hterm : ∀ n : ℕ, ((binomialSeries ℝ (-1/2 : ℝ) n) fun _ => -4 * y)
    = (Nat.centralBinom n : ℝ) * y ^ n := by
    intro n
    rw [binomialSeries_coeff]
    have hcn := choose_neg_half_mul n
    have : Ring.choose (-1/2 : ℝ) n * (-4 * y) ^ n
      = (Ring.choose (-1/2 : ℝ) n * (-4) ^ n) * y ^ n := by ring
    rw [this, hcn]
  simp_rw [hterm] at hbase
  have hpos : (0 : ℝ) < 1 - 4 * y := by
    have h1 : |(4 : ℝ) * y| < 1 := by
      have h2 : |(4 : ℝ) * y| = 4 * |y| := by rw [abs_mul]; norm_num
      rw [h2]
      linarith
    have := abs_lt.mp h1
    linarith
  have hval : ((1 : ℝ) + -4 * y) ^ (-1/2 : ℝ) = 1 / Real.sqrt (1 - 4 * y) := by
    have heq : (1 : ℝ) + -4 * y = 1 - 4 * y := by ring
    rw [heq]
    have hpos' : (0 : ℝ) ≤ 1 - 4 * y := le_of_lt hpos
    have e1 : (-1/2 : ℝ) = -((1/2 : ℝ)) := by ring
    rw [e1, Real.rpow_neg hpos', Real.sqrt_eq_rpow, inv_eq_one_div]
  rwa [hval] at hbase

end MetaMathlibExt

namespace MetaMathlibExt

/--
[harmonic_nonnegR](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma harmonic_nonnegR (n : ℕ) : (0 : ℝ) ≤ ((harmonic n : ℚ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := harmonic_succ n
    have h1 : ((harmonic (n+1) : ℚ) : ℝ)
      = ((harmonic n : ℚ) : ℝ) + (((n+1 : ℕ) : ℚ) : ℝ)⁻¹ := by
      rw [h]; push_cast; ring
    rw [h1]
    positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[harmonic_leR](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma harmonic_leR (n : ℕ) : (((harmonic n : ℚ) : ℝ)) ≤ (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := harmonic_succ n
    have h1 : ((harmonic (n+1) : ℚ) : ℝ)
      = ((harmonic n : ℚ) : ℝ) + (((n+1 : ℕ) : ℚ) : ℝ)⁻¹ := by
      rw [h]; push_cast; ring
    rw [h1]
    have h2 : ((((n+1 : ℕ) : ℚ)) : ℝ)⁻¹ ≤ 1 := by
      have hle : (1:ℝ) ≤ (((n+1 : ℕ) : ℚ) : ℝ) := by
        have : (1:ℕ) ≤ n+1 := Nat.le_add_left 1 n
        exact_mod_cast this
      calc ((((n+1 : ℕ) : ℚ)) : ℝ)⁻¹ ≤ (1:ℝ)⁻¹ := inv_anti₀ (by norm_num) hle
        _ = 1 := inv_one
    have hcast : (((n+1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coeff_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma coeff_recurrence (n : ℕ) :
  ((n : ℝ) + 1) * ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ))
    = 2 * (2 * (n : ℝ) + 1) * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))
      + (Nat.centralBinom (n+1) : ℝ) := by
  have hcb := Nat.succ_mul_centralBinom_succ n
  have hcbR : ((n : ℝ) + 1) * ((Nat.centralBinom (n + 1) : ℕ) : ℝ)
    = 2 * (2 * (n : ℝ) + 1) * ((Nat.centralBinom n : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hcb
    push_cast at h ⊢
    linarith [h]
  have hh := harmonic_succ n
  have hhR : ((harmonic (n+1) : ℚ) : ℝ)
    = ((harmonic n : ℚ) : ℝ) + (((n+1 : ℕ) : ℚ) : ℝ)⁻¹ := by
    rw [hh]; push_cast; ring
  have hcast : ((((n+1 : ℕ) : ℚ)) : ℝ) = (n : ℝ) + 1 := by norm_cast
  have hexpand : ((n : ℝ) + 1) * ((Nat.centralBinom (n+1) : ℝ) *
    (((harmonic n : ℚ) : ℝ) + ((((n+1 : ℕ) : ℚ)) : ℝ)⁻¹))
    = (((n : ℝ) + 1) * (Nat.centralBinom (n+1) : ℝ)) * ((harmonic n : ℚ) : ℝ)
      + (Nat.centralBinom (n+1) : ℝ) := by
    rw [hcast]
    field_simp
  have hcbR2 : ((n : ℝ) + 1) * ((Nat.centralBinom (n+1) : ℕ) : ℝ)
    = 2 * (2 * (n : ℝ) + 1) * ((Nat.centralBinom n : ℕ) : ℝ) := hcbR
  rw [hhR, hexpand, hcbR2]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ode_term](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma ode_term (n : ℕ) (y : ℝ) :
  ((n : ℝ) + 1) * ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y^(n+1)
    - 4 * ((n : ℝ) * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) * y^(n+1))
    - 2 * (((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) * y^(n+1))
    = (Nat.centralBinom (n+1) : ℝ) * y^(n+1) := by
  have h := coeff_recurrence n
  have heq : ((n : ℝ) + 1) * ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ))
    - 4 * ((n : ℝ) * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)))
    - 2 * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))
    = (Nat.centralBinom (n+1) : ℝ) := by linarith [h]
  calc ((n : ℝ) + 1) * ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y^(n+1)
    - 4 * ((n : ℝ) * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) * y^(n+1))
    - 2 * (((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) * y^(n+1))
    = (((n : ℝ) + 1) * ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ))
      - 4 * ((n : ℝ) * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)))
      - 2 * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))) * y^(n+1) := by ring
    _ = (Nat.centralBinom (n+1) : ℝ) * y^(n+1) := by rw [heq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[shift_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma shift_hasSum (f : ℕ → ℝ) (g : ℝ) (h : HasSum f g) :
  HasSum (fun n : ℕ => f (n + 1)) (g - f 0) := by
  have h2 := (hasSum_nat_add_iff' (f := f) (g := g) (k := 1)).mpr h
  simpa using h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unshift_hasSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma unshift_hasSum_zero (f : ℕ → ℝ) (S : ℝ) (h0 : f 0 = 0)
  (h : HasSum (fun n : ℕ => f (n + 1)) S) : HasSum f S := by
  have h2 : HasSum (fun n : ℕ => f (n + 1)) (S + f 0 - ∑ i ∈ Finset.range 1, f i) := by
    rw [Finset.sum_range_one]
    have hS : S + f 0 - f 0 = S := by rw [h0]; simp
    rwa [hS]
  have h3 := (hasSum_nat_add_iff' (f := f) (g := S + f 0) (k := 1)).mp h2
  rwa [h0, add_zero] at h3

end MetaMathlibExt

namespace MetaMathlibExt

/--
[summable_centralHarm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma summable_centralHarm_bound (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1 / 4) :
  Summable (fun n : ℕ => ‖(FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) n)‖ * q ^ n) := by
  have h4q : ‖(4 : ℝ) * q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_mul]
    norm_num
    rw [abs_of_nonneg hq0]
    linarith
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * ((4 : ℝ) * q) ^ n) := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (4 : ℝ) * q) h4q
    exact h.summable
  apply Summable.of_nonneg_of_le (f := fun n : ℕ => (n : ℝ) * ((4 : ℝ) * q) ^ n)
  · intro n
    positivity
  · intro n
    rw [FormalMultilinearSeries.ofScalars_norm]
    rw [Real.norm_eq_abs]
    have hcb : ((Nat.centralBinom n : ℝ)) ≤ (4 ^ n : ℝ) := by
      exact_mod_cast Nat.centralBinom_le_four_pow n
    have hcb_nn : (0:ℝ) ≤ (Nat.centralBinom n : ℝ) := by positivity
    have hH_nn := harmonic_nonnegR n
    have hH_le := harmonic_leR n
    have habs : |(Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)|
      = (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) := by
      apply abs_of_nonneg
      exact mul_nonneg hcb_nn hH_nn
    rw [habs]
    calc (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * q ^ n
      ≤ (4 ^ n : ℝ) * (n : ℝ) * q ^ n := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq0 n)
        exact mul_le_mul hcb hH_le hH_nn (by positivity)
      _ = (n : ℝ) * ((4 : ℝ) * q) ^ n := by ring
  · exact hgeo

end MetaMathlibExt

namespace MetaMathlibExt

/--
[radius_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma radius_ge (r : NNReal) (hr : (r : ℝ) < 1 / 4) :
  (r : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hr0 : (0:ℝ) ≤ (r : ℝ) := r.coe_nonneg
  have h := summable_centralHarm_bound (r : ℝ) hr0 hr
  simpa using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[radius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma radius_pos :
  0 < (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius := by
  set r0 : NNReal := ⟨1 / 8, by norm_num⟩ with hr0
  have h18 : (r0 : ℝ) < 1 / 4 := by
    have : (r0 : ℝ) = 1 / 8 := rfl
    rw [this]; norm_num
  have h := radius_ge r0 h18
  have hpos : (0:ENNReal) < (r0 : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pos]
    have hrr : (r0 : ℝ) = 1 / 8 := rfl
    rw [hrr]; norm_num
  exact lt_of_lt_of_le hpos h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mem_radius_of_abs_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma mem_radius_of_abs_lt (q : ℝ) (hq0 : 0 ≤ q) (hq14 : q < 1 / 4)
  (y : ℝ) (hy : |y| < q) :
  y ∈ Metric.eball (0 : ℝ)
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius := by
  set rNN : NNReal := ⟨q, hq0⟩ with hrNN
  have hqeq : (rNN : ℝ) = q := rfl
  have h14 : (rNN : ℝ) < 1 / 4 := by rw [hqeq]; exact hq14
  have hrad : (rNN : ENNReal)
    ≤ (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius :=
    radius_ge rNN h14
  have hmem0 : y ∈ Metric.eball (0 : ℝ) (rNN : ENNReal) := by
    have h1 : |y| < (rNN : ℝ) := by rw [hqeq]; exact hy
    have hpos0 : (0 : ℝ) < (rNN : ℝ) := by
      rw [hqeq]
      exact lt_of_le_of_lt (abs_nonneg y) hy
    rw [Metric.mem_eball, edist_dist, dist_zero_right, Real.norm_eq_abs,
      ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hpos0]
    exact h1
  exact Metric.eball_subset_eball hrad hmem0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hasSum_F](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma hasSum_F (y : ℝ) (hy : |y| < 1 / 4) :
  HasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * y ^ n)
    ((FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y) := by
  have hball := (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).hasFPowerSeriesOnBall
    radius_pos
  obtain ⟨q, hqy, hq14⟩ : ∃ q : ℝ, |y| < q ∧ q < 1 / 4 := exists_between hy
  have hq0 : 0 ≤ q := le_trans (abs_nonneg y) (le_of_lt hqy)
  set rNN : NNReal := ⟨q, hq0⟩ with hrNN
  have hqeq : (rNN : ℝ) = q := rfl
  have h14 : (rNN : ℝ) < 1 / 4 := by rw [hqeq]; exact hq14
  have hrad : (rNN : ENNReal)
    ≤ (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius :=
    radius_ge rNN h14
  have hmem0 : y ∈ Metric.eball (0 : ℝ) (rNN : ENNReal) := by
    have h1 : |y| < (rNN : ℝ) := by rw [hqeq]; exact hqy
    have hpos0 : (0:ℝ) < (rNN : ℝ) := by
      rw [hqeq]; exact lt_of_le_of_lt (abs_nonneg y) hqy
    rw [Metric.mem_eball, edist_dist, dist_zero_right, Real.norm_eq_abs,
      ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hpos0]
    exact h1
  have hmem : y ∈ Metric.eball (0 : ℝ)
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius :=
    Metric.eball_subset_eball hrad hmem0
  have hsum := hball.hasSum_sub hmem
  simp only [sub_zero] at hsum
  have hterm : ∀ n : ℕ, ((FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) n) fun _ => y)
    = (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * y ^ n := by
    intro n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]
  simpa [hterm] using hsum

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hasSum_yF'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma hasSum_yF' (y : ℝ)
  (hmem : y ∈ Metric.eball (0 : ℝ)
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius) :
  HasSum (fun n : ℕ => ((n : ℝ) + 1) *
    ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y ^ (n + 1))
    ((fderiv ℝ (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y) y) := by
  have hball : HasFPowerSeriesOnBall
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)))
    0
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius :=
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).hasFPowerSeriesOnBall
      radius_pos
  have hderiv := hball.fderiv
  have hsum := hderiv.hasSum_sub hmem
  simp only [sub_zero] at hsum
  have hmap := ((ContinuousLinearMap.apply ℝ ℝ) y).hasSum hsum
  have hmap2 : HasSum (fun n : ℕ => ((((FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).derivSeries n)
    fun _ => y) y))
    (((fderiv ℝ (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y) y)) := by
    simpa only [ContinuousLinearMap.apply_apply] using hmap
  have hterm : ∀ n : ℕ, ((n : ℝ) + 1) *
    ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y ^ (n + 1)
    = ((((FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).derivSeries n)
      fun _ => y) y) := by
    intro n
    rw [FormalMultilinearSeries.derivSeries_apply_diag]
    simp only [nsmul_eq_mul]
    have happ : (((FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))) (n+1))
      fun _ => y)
      = (Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ) * y ^ (n+1) := by
      rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]
    rw [happ]
    push_cast
    ring
  exact hmap2.congr_fun hterm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ode_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma ode_mul (y F E G : ℝ)
  (hF : HasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * y ^ n) F)
  (hE : HasSum (fun n : ℕ => ((n : ℝ) + 1) *
    ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y ^ (n + 1)) E)
  (hG : HasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) * y ^ n) G) :
  E - 4 * (y * E) - 2 * (y * F) = G - 1 := by
  have h_yE : HasSum (fun n : ℕ => (n : ℝ) *
    ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) * y ^ (n + 1)) (y * E) := by
    have hEm : HasSum (fun n : ℕ => y * (((n : ℝ) + 1) *
      ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y ^ (n + 1)))
      (y * E) := hE.mul_left y
    have hshift : (fun n : ℕ => y * (((n : ℝ) + 1) *
      ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y ^ (n + 1)))
      = (fun n : ℕ => ((fun m : ℕ => (m : ℝ) *
        ((Nat.centralBinom m : ℝ) * ((harmonic m : ℚ) : ℝ)) * y ^ (m + 1))) (n + 1)) := by
      funext n
      push_cast
      ring
    rw [hshift] at hEm
    have h0 : ((fun m : ℕ => (m : ℝ) *
      ((Nat.centralBinom m : ℝ) * ((harmonic m : ℚ) : ℝ)) * y ^ (m + 1))) 0 = 0 := by simp
    exact unshift_hasSum_zero _ _ h0 hEm
  have h_yF : HasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * y ^ (n + 1))
    (y * F) := by
    have h2 := hF.mul_left y
    refine h2.congr_fun (fun n => ?_)
    ring
  have h_G1 : HasSum (fun n : ℕ => (Nat.centralBinom (n + 1) : ℝ) * y ^ (n + 1)) (G - 1) := by
    have hsh := shift_hasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) * y ^ n) G hG
    have hb0 : (Nat.centralBinom 0 : ℝ) * y ^ (0 : ℕ) = 1 := by
      simp [Nat.centralBinom_zero]
    have heq : G - ((Nat.centralBinom 0 : ℝ) * y ^ (0 : ℕ)) = G - 1 := by rw [hb0]
    rwa [heq] at hsh
  have hLHS : HasSum (fun n : ℕ => ((n : ℝ) + 1) *
    ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y ^ (n + 1)
    - 4 * ((n : ℝ) * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) * y ^ (n + 1))
    - 2 * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * y ^ (n + 1)))
    (E - 4 * (y * E) - 2 * (y * F)) := by
    exact (hE.sub (h_yE.mul_left 4)).sub (h_yF.mul_left 2)
  have hRHS : HasSum (fun n : ℕ => ((n : ℝ) + 1) *
    ((Nat.centralBinom (n+1) : ℝ) * ((harmonic (n+1) : ℚ) : ℝ)) * y ^ (n + 1)
    - 4 * ((n : ℝ) * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) * y ^ (n + 1))
    - 2 * ((Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * y ^ (n + 1)))
    (G - 1) := by
    refine h_G1.congr_fun (fun n => ?_)
    exact ode_term n y
  exact hLHS.unique hRHS

end MetaMathlibExt

namespace MetaMathlibExt

/--
[F_fderiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma F_fderiv_apply (y : ℝ) :
  (fderiv ℝ (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y) y
    = y * deriv (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y := by
  rw [fderiv_eq_deriv_mul, mul_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[F_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma F_differentiableAt (y : ℝ)
  (hmem : y ∈ Metric.eball (0 : ℝ)
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius) :
  DifferentiableAt ℝ (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y := by
  have hball := (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).hasFPowerSeriesOnBall
    radius_pos
  have hdiff : DifferentiableWithinAt ℝ (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum
    (Metric.eball (0 : ℝ)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius)
    y :=
    hball.differentiableOn y hmem
  exact hdiff.differentiableAt (Metric.isOpen_eball.mem_nhds hmem)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ode_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma ode_div (y : ℝ) (hy : |y| < 1 / 4) (hy0 : y ≠ 0)
  (hmem : y ∈ Metric.eball (0 : ℝ)
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius) :
  (1 - 4 * y) * deriv (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y
    - 2 * (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y
    = 4 / (Real.sqrt (1 - 4 * y) * (1 + Real.sqrt (1 - 4 * y))) := by
  have hF := hasSum_F y hy
  have hE := hasSum_yF' y hmem
  have hG := hasSum_centralBinom y hy
  have hode := ode_mul y
    ((FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y)
    ((fderiv ℝ (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y) y)
    (1 / Real.sqrt (1 - 4 * y)) hF hE hG
  have hE_eq := F_fderiv_apply y
  rw [hE_eq] at hode
  have hpos : (0 : ℝ) < 1 - 4 * y := by
    have h1 : |(4 : ℝ) * y| < 1 := by
      have h2 : |(4 : ℝ) * y| = 4 * |y| := by rw [abs_mul]; norm_num
      rw [h2]
      linarith
    have habs := abs_lt.mp h1
    linarith
  have hs_pos : (0 : ℝ) < Real.sqrt (1 - 4 * y) := Real.sqrt_pos.mpr hpos
  have hs_ne : Real.sqrt (1 - 4 * y) ≠ 0 := ne_of_gt hs_pos
  have hs_sq : Real.sqrt (1 - 4 * y) ^ 2 = 1 - 4 * y :=
    Real.sq_sqrt (le_of_lt hpos)
  have h1s_ne : (1 : ℝ) + Real.sqrt (1 - 4 * y) ≠ 0 := by
    have h1s_pos : (0 : ℝ) < 1 + Real.sqrt (1 - 4 * y) := by linarith [hs_pos]
    exact ne_of_gt h1s_pos
  have hmul : y * ((1 - 4 * y) * deriv (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y
    - 2 * (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y)
    = 1 / Real.sqrt (1 - 4 * y) - 1 := by
    linear_combination hode
  have hdiv : (1 - 4 * y) * deriv (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y
    - 2 * (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y
    = (1 / Real.sqrt (1 - 4 * y) - 1) / y := by
    rw [eq_div_iff_mul_eq hy0]
    linear_combination hmul
  rw [hdiv]
  have hEq : (1 / Real.sqrt (1 - 4 * y) - 1) / y
    = 4 / (Real.sqrt (1 - 4 * y) * (1 + Real.sqrt (1 - 4 * y))) := by
    field_simp
    nlinarith [hs_sq]
  exact hEq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[F_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma F_zero :
  (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum 0 = 0 := by
  have h0lt : |(0 : ℝ)| < 1 / 4 := by norm_num
  have hF0 := hasSum_F 0 h0lt
  have hfn : ∀ n : ℕ, (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * (0 : ℝ) ^ n = 0 := by
    intro n
    cases n with
    | zero => simp
    | succ n =>
      have h0pow : (0 : ℝ) ^ (n + 1) = 0 := zero_pow (Nat.succ_ne_zero n)
      rw [h0pow, mul_zero]
  have hHas0 : HasSum
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * (0 : ℝ) ^ n) 0 :=
    hasSum_zero.congr_fun (fun n => hfn n)
  exact hF0.unique hHas0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[D_hasDeriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma D_hasDeriv_zero (y : ℝ) (hy : |y| < 1 / 4) (hy0 : y ≠ 0)
  (hmem : y ∈ Metric.eball (0 : ℝ)
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius) :
  HasDerivAt (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) 0 y := by
  have hpos : (0 : ℝ) < 1 - 4 * y := by
    have h1 : |(4 : ℝ) * y| < 1 := by
      have h2 : |(4 : ℝ) * y| = 4 * |y| := by rw [abs_mul]; norm_num
      rw [h2]
      linarith
    have habs := abs_lt.mp h1
    linarith
  have hs_pos : (0 : ℝ) < Real.sqrt (1 - 4 * y) := Real.sqrt_pos.mpr hpos
  have hs_ne : Real.sqrt (1 - 4 * y) ≠ 0 := ne_of_gt hs_pos
  have h_inner_ne : (1 : ℝ) - 4 * y ≠ 0 := ne_of_gt hpos
  have h1s_ne : (1 : ℝ) + Real.sqrt (1 - 4 * y) ≠ 0 := by
    have h1s_pos : (0 : ℝ) < 1 + Real.sqrt (1 - 4 * y) := by linarith [hs_pos]
    exact ne_of_gt h1s_pos
  have h2s_ne : (2 : ℝ) * Real.sqrt (1 - 4 * y) ≠ 0 :=
    mul_ne_zero two_ne_zero hs_ne
  have hLarg_ne : (1 + Real.sqrt (1 - 4 * y)) / (2 * Real.sqrt (1 - 4 * y)) ≠ 0 :=
    div_ne_zero h1s_ne h2s_ne
  have hF_diff := F_differentiableAt y hmem
  have hF_deriv : HasDerivAt (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum
    (deriv (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y) y :=
    hF_diff.hasDerivAt
  have h_id : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id' y
  have h_4y : HasDerivAt (fun y : ℝ => 4 * y) (4 * 1) y := h_id.const_mul 4
  have h_inner : HasDerivAt (fun y : ℝ => 1 - 4 * y) (-(4 * 1)) y :=
    h_4y.const_sub 1
  have h_inner4 : HasDerivAt (fun y : ℝ => 1 - 4 * y) (-4) y := by
    simpa using h_inner
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - 4 * y))
    (-4 / (2 * Real.sqrt (1 - 4 * y))) y :=
    h_inner4.sqrt h_inner_ne
  have h_one : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
  have hN := h_one.add hs
  have hDn := hs.const_mul 2
  have hDiv := hN.fun_div hDn h2s_ne
  have hLog := hDiv.log hLarg_ne
  have h2Log := hLog.const_mul 2
  have hMul := hs.mul hF_deriv
  have hD := hMul.sub h2Log
  have hderiv : deriv (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) y = 0 := by
    have hderiv_eq : deriv (fun t : ℝ => Real.sqrt (1 - 4 * t) *
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
      - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
        (2 * Real.sqrt (1 - 4 * t)))) y = _ := hD.deriv
    rw [hderiv_eq]
    simp only [Pi.add_apply, zero_add]
    have hODE := ode_div y hy hy0 hmem
    have hs_sq : Real.sqrt (1 - 4 * y) ^ 2 = 1 - 4 * y :=
      Real.sq_sqrt (le_of_lt hpos)
    have hODE_mul : (((1 - 4 * y) * deriv (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y
      - 2 * (FormalMultilinearSeries.ofScalars ℝ
        (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y)
      * (Real.sqrt (1 - 4 * y) * (1 + Real.sqrt (1 - 4 * y)))) = 4 := by
      rw [hODE]
      field_simp
    field_simp
    linear_combination 2 * hODE_mul + (2 * Real.sqrt (1 - 4 * y)
      * (1 + Real.sqrt (1 - 4 * y)) * deriv (FormalMultilinearSeries.ofScalars ℝ
        (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum y) * hs_sq
  have hderiv_eq : deriv (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) y = _ := hD.deriv
  have hD'_eq : _ = (0 : ℝ) := hderiv_eq.symm.trans hderiv
  exact hD.congr_deriv hD'_eq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[F_deriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma F_deriv_zero :
  deriv (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum 0 = 2 := by
  have hball := (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).hasFPowerSeriesOnBall
    radius_pos
  have hball_fderiv := hball.fderiv
  have hcoeff := hball_fderiv.coeff_zero (fun _ : Fin 0 => (1 : ℝ))
  have hdiag := FormalMultilinearSeries.derivSeries_apply_diag
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))) 0 (1 : ℝ)
  have hcongr := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcoeff
  have hEq : (fderiv ℝ (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum 0) 1
    = (0 + 1) • ((FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))) 1
      fun _ => (1 : ℝ)) := by
    have h1 := hcongr.symm.trans hdiag
    exact h1
  have hderiv_eq : (fderiv ℝ (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum 0) 1
    = deriv (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum 0 :=
    fderiv_apply_one_eq_deriv
  have hRHS : (0 + 1) • ((FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))) 1
    fun _ => (1 : ℝ)) = 2 := by
    have happ := FormalMultilinearSeries.ofScalars_apply_eq (E := ℝ)
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ)) (1 : ℝ) 1
    have hcb1 : (Nat.centralBinom 1 : ℝ) = 2 := by
      have h : Nat.centralBinom 1 = 2 := rfl
      exact_mod_cast h
    have hH1 : ((harmonic 1 : ℚ) : ℝ) = 1 := by
      have h : harmonic 1 = 1 := by simp
      rw [h]
      norm_num
    simp only [happ, smul_eq_mul, pow_one, mul_one] at ⊢
    rw [hcb1, hH1]
    norm_num
  exact hderiv_eq.symm.trans (hEq.trans hRHS)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[D_hasDeriv_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma D_hasDeriv_at_zero :
  HasDerivAt (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) 0 0 := by
  have hmem0 : (0 : ℝ) ∈ Metric.eball (0 : ℝ)
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).radius :=
    Metric.mem_eball_self radius_pos
  have hpos : (0 : ℝ) < 1 - 4 * (0 : ℝ) := by norm_num
  have hs_pos : (0 : ℝ) < Real.sqrt (1 - 4 * (0 : ℝ)) := Real.sqrt_pos.mpr hpos
  have hs_ne : Real.sqrt (1 - 4 * (0 : ℝ)) ≠ 0 := ne_of_gt hs_pos
  have h_inner_ne : (1 : ℝ) - 4 * (0 : ℝ) ≠ 0 := ne_of_gt hpos
  have h1s_ne : (1 : ℝ) + Real.sqrt (1 - 4 * (0 : ℝ)) ≠ 0 := by
    have h1s_pos : (0 : ℝ) < 1 + Real.sqrt (1 - 4 * (0 : ℝ)) := by
      linarith [hs_pos]
    exact ne_of_gt h1s_pos
  have h2s_ne : (2 : ℝ) * Real.sqrt (1 - 4 * (0 : ℝ)) ≠ 0 :=
    mul_ne_zero two_ne_zero hs_ne
  have hLarg_ne : (1 + Real.sqrt (1 - 4 * (0 : ℝ))) /
    (2 * Real.sqrt (1 - 4 * (0 : ℝ))) ≠ 0 :=
    div_ne_zero h1s_ne h2s_ne
  have hF_diff := F_differentiableAt 0 hmem0
  have hF_deriv : HasDerivAt (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum
    (deriv (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum 0) 0 :=
    hF_diff.hasDerivAt
  have h_id : HasDerivAt (fun y : ℝ => y) 1 (0 : ℝ) := hasDerivAt_id' 0
  have h_4y : HasDerivAt (fun y : ℝ => 4 * y) (4 * 1) (0 : ℝ) := h_id.const_mul 4
  have h_inner : HasDerivAt (fun y : ℝ => 1 - 4 * y) (-(4 * 1)) (0 : ℝ) :=
    h_4y.const_sub 1
  have h_inner4 : HasDerivAt (fun y : ℝ => 1 - 4 * y) (-4) (0 : ℝ) := by
    simpa using h_inner
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - 4 * y))
    (-4 / (2 * Real.sqrt (1 - 4 * (0 : ℝ)))) (0 : ℝ) :=
    h_inner4.sqrt h_inner_ne
  have h_one : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 (0 : ℝ) :=
    hasDerivAt_const 0 1
  have hN := h_one.add hs
  have hDn := hs.const_mul 2
  have hDiv := hN.fun_div hDn h2s_ne
  have hLog := hDiv.log hLarg_ne
  have h2Log := hLog.const_mul 2
  have hMul := hs.mul hF_deriv
  have hD := hMul.sub h2Log
  have hderiv : deriv (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) 0 = 0 := by
    have hderiv_eq : deriv (fun t : ℝ => Real.sqrt (1 - 4 * t) *
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
      - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
        (2 * Real.sqrt (1 - 4 * t)))) 0 = _ := hD.deriv
    rw [hderiv_eq]
    simp only [Pi.add_apply, zero_add]
    rw [F_zero, F_deriv_zero]
    have hsqrt1 : Real.sqrt (1 - 4 * (0 : ℝ)) = 1 := by
      have h10 : (1 : ℝ) - 4 * (0 : ℝ) = 1 := by ring
      rwa [h10]
    rw [hsqrt1]
    norm_num
  have hderiv_eq : deriv (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) 0 = _ := hD.deriv
  have hD'_eq : _ = (0 : ℝ) := hderiv_eq.symm.trans hderiv
  exact hD.congr_deriv hD'_eq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hasSum_centralBinomial_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
lemma hasSum_centralBinomial_harmonic
  {x : ℝ}
-- given
  (hx : |x| < 1 / 4) :
-- imply
  HasSum
    (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) * (harmonic (n + 1) : ℝ) *
    x ^ (n + 1))
    (2 / Real.sqrt (1 - 4 * x) *
    Real.log ((1 + Real.sqrt (1 - 4 * x)) / (2 * Real.sqrt (1 - 4 * x)))) := by
-- proof
  obtain ⟨q, hqy, hq14⟩ : ∃ q : ℝ, |x| < q ∧ q < 1 / 4 := exists_between hx
  have hq0 : 0 ≤ q := le_trans (abs_nonneg x) (le_of_lt hqy)
  have hqpos : 0 < q := lt_of_le_of_lt (abs_nonneg x) hqy
  have hHasDeriv : ∀ y ∈ Set.Ioo (-q) q,
    HasDerivAt (fun t : ℝ => Real.sqrt (1 - 4 * t) *
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
      - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
        (2 * Real.sqrt (1 - 4 * t)))) 0 y := by
    intro y hy
    have hy_mem : -q < y ∧ y < q := Set.mem_Ioo.mp hy
    have hyq : |y| < q := abs_lt.mpr hy_mem
    have hy14 : |y| < 1 / 4 := lt_trans hyq hq14
    have hmem_y := mem_radius_of_abs_lt q hq0 hq14 y hyq
    obtain rfl | hy0 := eq_or_ne y 0
    · exact D_hasDeriv_at_zero
    · exact D_hasDeriv_zero y hy14 hy0 hmem_y
  have hDiffOn : DifferentiableOn ℝ (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) (Set.Ioo (-q) q) := by
    intro y hy
    exact (hHasDeriv y hy).differentiableAt.differentiableWithinAt
  have hDerivEq : Set.EqOn (deriv (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t))))) 0 (Set.Ioo (-q) q) := by
    intro y hy
    exact (hHasDeriv y hy).deriv
  have hx_mem : x ∈ Set.Ioo (-q) q := Set.mem_Ioo.mpr (abs_lt.mp hqy)
  have h0_mem : (0 : ℝ) ∈ Set.Ioo (-q) q :=
    Set.mem_Ioo.mpr ⟨by linarith [hqpos], hqpos⟩
  have hconst := IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
    hDiffOn hDerivEq hx_mem h0_mem
  have hD0 : (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) 0 = 0 := by
    change Real.sqrt (1 - 4 * (0 : ℝ)) *
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum 0
      - 2 * Real.log ((1 + Real.sqrt (1 - 4 * (0 : ℝ))) /
        (2 * Real.sqrt (1 - 4 * (0 : ℝ)))) = 0
    have hsqrt1 : Real.sqrt (1 - 4 * (0 : ℝ)) = 1 := by
      have h10 : (1 : ℝ) - 4 * (0 : ℝ) = 1 := by ring
      rwa [h10]
    rw [hsqrt1, F_zero]
    have hLarg1 : ((1 : ℝ) + 1) / (2 * 1) = 1 := by norm_num
    rw [hLarg1, Real.log_one]
    ring
  have hDx0 : (fun t : ℝ => Real.sqrt (1 - 4 * t) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum t
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * t)) /
      (2 * Real.sqrt (1 - 4 * t)))) x = 0 :=
    hconst.trans hD0
  have hDx' : Real.sqrt (1 - 4 * x) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum x
    - 2 * Real.log ((1 + Real.sqrt (1 - 4 * x)) /
      (2 * Real.sqrt (1 - 4 * x))) = 0 :=
    hDx0
  have hpos_x : (0 : ℝ) < 1 - 4 * x := by
    have h1 : |(4 : ℝ) * x| < 1 := by
      have h2 : |(4 : ℝ) * x| = 4 * |x| := by rw [abs_mul]; norm_num
      rw [h2]
      linarith
    have habs := abs_lt.mp h1
    linarith
  have hsx_pos : (0 : ℝ) < Real.sqrt (1 - 4 * x) := Real.sqrt_pos.mpr hpos_x
  have hsx_ne : Real.sqrt (1 - 4 * x) ≠ 0 := ne_of_gt hsx_pos
  have hEq : Real.sqrt (1 - 4 * x) *
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum x
    = 2 * Real.log ((1 + Real.sqrt (1 - 4 * x)) /
      (2 * Real.sqrt (1 - 4 * x))) :=
    sub_eq_zero.mp hDx'
  have hF_eq : (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum x
    = 2 * Real.log ((1 + Real.sqrt (1 - 4 * x)) /
      (2 * Real.sqrt (1 - 4 * x))) / Real.sqrt (1 - 4 * x) := by
    rw [eq_div_iff_mul_eq hsx_ne]
    rwa [mul_comm]
  have hclosed : (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ))).sum x
    = 2 / Real.sqrt (1 - 4 * x) *
      Real.log ((1 + Real.sqrt (1 - 4 * x)) /
        (2 * Real.sqrt (1 - 4 * x))) := by
    rw [hF_eq]
    ring
  have hF := hasSum_F x hx
  rw [hclosed] at hF
  have h0 : (Nat.centralBinom 0 : ℝ) * ((harmonic 0 : ℚ) : ℝ) * x ^ (0 : ℕ) = 0 := by
    simp
  have hTail := shift_hasSum
    (fun n : ℕ => (Nat.centralBinom n : ℝ) * ((harmonic n : ℚ) : ℝ) * x ^ n)
    (2 / Real.sqrt (1 - 4 * x) *
      Real.log ((1 + Real.sqrt (1 - 4 * x)) / (2 * Real.sqrt (1 - 4 * x)))) hF
  have hTail' : HasSum (fun n : ℕ => (Nat.centralBinom (n + 1) : ℝ) *
    ((harmonic (n + 1) : ℚ) : ℝ) * x ^ (n + 1))
    (2 / Real.sqrt (1 - 4 * x) *
      Real.log ((1 + Real.sqrt (1 - 4 * x)) /
        (2 * Real.sqrt (1 - 4 * x)))) := by
    simpa [h0] using hTail
  exact hTail'
end MetaMathlibExt



-- created on 2026-10-20
-- updated on 2026-10-23
