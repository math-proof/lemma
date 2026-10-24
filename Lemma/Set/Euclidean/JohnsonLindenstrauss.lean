import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.JohnsonLindenstrauss
open scoped RealInnerProductSpace
open ProbabilityTheory MeasureTheory
open MathlibExt.Geometry.Euclidean.JohnsonLindenstraussWanted


/--
[mgf_sq_stdGaussian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma mgf_sq_stdGaussian (t : ℝ) :
  mgf (fun x : ℝ => x ^ 2) (gaussianReal 0 1) t =
    (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [mgf, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    (∫ x : ℝ, (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
      Real.exp (t * x ^ 2)) =
      (√(2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-((1 - 2 * t) / 2) * x ^ 2) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    _ = (Real.sqrt (1 - 2 * t))⁻¹ := by
      rw [integral_gaussian]
      by_cases h : 0 < 1 - 2 * t
      · rw [Real.sqrt_div (by positivity : 0 ≤ Real.pi)]
        rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
        rw [Real.sqrt_div h.le]
        have htwo : Real.sqrt 2 ≠ 0 := by positivity
        have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
        have hone : Real.sqrt (1 - 2 * t) ≠ 0 := by positivity
        field_simp
      · have hb : (1 - 2 * t) / 2 ≤ 0 := by linarith
        have hs : Real.sqrt (1 - 2 * t) = 0 :=
          Real.sqrt_eq_zero_of_nonpos (le_of_not_gt h)
        have hq : Real.pi / ((1 - 2 * t) / 2) ≤ 0 :=
          div_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hb
        rw [Real.sqrt_eq_zero_of_nonpos hq, hs]
        simp

/--
[mgf_sum_sq_pi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma mgf_sum_sq_pi (d : ℕ) (t : ℝ) :
  mgf (fun ω : Fin d → ℝ => ∑ i, (ω i) ^ 2)
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) t =
    (Real.sqrt (1 - 2 * t))⁻¹ ^ d := by
  let X : Fin d → (Fin d → ℝ) → ℝ := fun i ω => (ω i) ^ 2
  have hIndep : iIndepFun X (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    exact iIndepFun_pi (μ := fun _ : Fin d => gaussianReal 0 1)
      (X := fun _ x => x ^ 2) (fun _ => by fun_prop)
  have hMeas : ∀ i, Measurable (X i) := by
    intro i
    fun_prop
  have hfun : (fun ω : Fin d → ℝ => ∑ i, (ω i) ^ 2) = ∑ i ∈ Finset.univ, X i := by
    funext ω
    simp [X]
  rw [hfun, hIndep.mgf_sum hMeas Finset.univ]
  calc
    (∏ i ∈ Finset.univ, mgf (X i)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) t) =
      ∏ _i : Fin d, (Real.sqrt (1 - 2 * t))⁻¹ := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [mgf_congr_of_identDistrib (X i) (fun x : ℝ => x ^ 2) _ t]
      · exact mgf_sq_stdGaussian t
      · simpa [X, Function.comp_def] using
        ((measurePreserving_eval
          (fun _ : Fin d => gaussianReal 0 1) i).hasLaw.identDistrib
            (HasLaw.id : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1))).comp
              (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
    _ = (Real.sqrt (1 - 2 * t))⁻¹ ^ d := by simp

/--
[integrable_exp_mul_sq_stdGaussian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma integrable_exp_mul_sq_stdGaussian {t : ℝ} (ht : t < 1 / 2) :
  Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal,
    NNReal.coe_one, mul_one, sub_zero]
  have hb : 0 < (1 / 2 : ℝ) - t := by linarith
  convert (integrable_exp_neg_mul_sq hb).const_mul (Real.sqrt (2 * Real.pi))⁻¹ using 1
  funext x
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

/--
[integrable_exp_mul_sum_sq_pi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma integrable_exp_mul_sum_sq_pi (d : ℕ) {t : ℝ} (ht : t < 1 / 2) :
  Integrable (fun ω : Fin d → ℝ =>
    Real.exp (t * ∑ i, (ω i) ^ 2))
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  let X : Fin d → (Fin d → ℝ) → ℝ := fun i ω => (ω i) ^ 2
  have hIndep : iIndepFun X (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    exact iIndepFun_pi (μ := fun _ : Fin d => gaussianReal 0 1)
      (X := fun _ x => x ^ 2) (fun _ => by fun_prop)
  have hMeas : ∀ i, Measurable (X i) := by
    intro i
    fun_prop
  have hInt : ∀ i ∈ Finset.univ,
    Integrable (fun ω : Fin d → ℝ => Real.exp (t * X i ω))
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    intro i _hi
    simpa [X, Function.comp_def] using
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).integrable_comp_of_integrable
        (integrable_exp_mul_sq_stdGaussian ht)
  simpa [X] using
    hIndep.integrable_exp_mul_sum hMeas (s := Finset.univ) hInt

/--
[sum_sq_pi_upper_chernoff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma sum_sq_pi_upper_chernoff (d : ℕ) (ε t : ℝ)
  (ht0 : 0 ≤ t) (ht : t < 1 / 2) :
  (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
    {ω | (d : ℝ) * (1 + ε) ≤ ∑ i, (ω i) ^ 2} ≤
    Real.exp (-t * ((d : ℝ) * (1 + ε))) *
      (Real.sqrt (1 - 2 * t))⁻¹ ^ d := by
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
      {ω | (d : ℝ) * (1 + ε) ≤ ∑ i, (ω i) ^ 2} ≤
      Real.exp (-t * ((d : ℝ) * (1 + ε))) *
        mgf (fun ω : Fin d → ℝ => ∑ i, (ω i) ^ 2)
          (Measure.pi fun _ : Fin d => gaussianReal 0 1) t :=
      measure_ge_le_exp_mul_mgf _ ht0 (integrable_exp_mul_sum_sq_pi d ht)
    _ = _ := by rw [mgf_sum_sq_pi]

/--
[sum_sq_pi_lower_chernoff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma sum_sq_pi_lower_chernoff (d : ℕ) (ε t : ℝ)
  (ht : t ≤ 0) :
  (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
    {ω | (∑ i, (ω i) ^ 2) ≤ (d : ℝ) * (1 - ε)} ≤
    Real.exp (-t * ((d : ℝ) * (1 - ε))) *
      (Real.sqrt (1 - 2 * t))⁻¹ ^ d := by
  have ht' : t < 1 / 2 := by linarith
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
      {ω | (∑ i, (ω i) ^ 2) ≤ (d : ℝ) * (1 - ε)} ≤
      Real.exp (-t * ((d : ℝ) * (1 - ε))) *
        mgf (fun ω : Fin d → ℝ => ∑ i, (ω i) ^ 2)
          (Measure.pi fun _ : Fin d => gaussianReal 0 1) t :=
      measure_le_le_exp_mul_mgf _ ht (integrable_exp_mul_sum_sq_pi d ht')
    _ = _ := by rw [mgf_sum_sq_pi]

/--
[neg_log_one_sub_le_add_two_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma neg_log_one_sub_le_add_two_sq {u : ℝ}
  (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) :
  -Real.log (1 - u) ≤ u + 2 * u ^ 2 := by
  have habs : |u| < 1 := by rw [abs_of_nonneg hu0]; linarith
  have hTaylor := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, zero_add, pow_one, div_one] at hTaylor
  rw [abs_of_nonneg hu0] at hTaylor
  have hden : 0 < 1 - u := by linarith
  have hquot : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg u]
  have hneg : -(u + Real.log (1 - u)) ≤ |u + Real.log (1 - u)| :=
    neg_le_abs _
  linarith

/--
[sqrt_inv_pow_eq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma sqrt_inv_pow_eq_exp (d : ℕ) {a : ℝ} (ha : 0 < a) :
  (Real.sqrt a)⁻¹ ^ d =
    Real.exp (-((d : ℝ) / 2) * Real.log a) := by
  calc
    (Real.sqrt a)⁻¹ ^ d = Real.exp (-Real.log (Real.sqrt a)) ^ d := by
      rw [Real.exp_neg, Real.exp_log (Real.sqrt_pos.2 ha)]
    _ = Real.exp ((d : ℝ) * (-Real.log (Real.sqrt a))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-((d : ℝ) / 2) * Real.log a) := by
      rw [Real.log_sqrt ha.le]
      congr 1
      ring_nf

/--
[sum_sq_pi_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma sum_sq_pi_upper_tail (d : ℕ) {ε : ℝ}
  (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
  (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
    {ω | (d : ℝ) * (1 + ε) ≤ ∑ i, (ω i) ^ 2} ≤
    Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
  have ht0 : 0 ≤ ε / 8 := by positivity
  have ht : ε / 8 < 1 / 2 := by linarith
  have ha : 0 < 1 - 2 * (ε / 8) := by linarith
  have hu : ε / 4 ≤ 1 / 4 := by linarith
  have hlog := neg_log_one_sub_le_add_two_sq (u := ε / 4) (by positivity) hu
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
      {ω | (d : ℝ) * (1 + ε) ≤ ∑ i, (ω i) ^ 2} ≤
      Real.exp (-(ε / 8) * ((d : ℝ) * (1 + ε))) *
        (Real.sqrt (1 - 2 * (ε / 8)))⁻¹ ^ d :=
      sum_sq_pi_upper_chernoff d ε (ε / 8) ht0 ht
    _ = Real.exp (-(ε / 8) * ((d : ℝ) * (1 + ε)) -
      ((d : ℝ) / 2) * Real.log (1 - ε / 4)) := by
      rw [sqrt_inv_pow_eq_exp d ha, ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
      apply Real.exp_le_exp.mpr
      have hd : 0 ≤ (d : ℝ) := by positivity
      nlinarith

/--
[sub_sq_le_log_one_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma sub_sq_le_log_one_add {u : ℝ} (hu : 0 ≤ u) :
  u - u ^ 2 ≤ Real.log (1 + u) := by
  have hpos : 0 < 1 + u := by linarith
  have hbase := Real.one_sub_inv_le_log_of_pos hpos
  have hid : 1 - (1 + u)⁻¹ = u / (1 + u) := by
    field_simp
    ring
  rw [hid] at hbase
  apply le_trans ?_ hbase
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonneg hu (sq_nonneg u)]

/--
[sum_sq_pi_lower_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma sum_sq_pi_lower_tail (d : ℕ) {ε : ℝ}
  (hε0 : 0 ≤ ε) :
  (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
    {ω | (∑ i, (ω i) ^ 2) ≤ (d : ℝ) * (1 - ε)} ≤
    Real.exp (-((d : ℝ) * ε ^ 2 / 8)) := by
  have ht : -(ε / 4) ≤ 0 := neg_nonpos.mpr (div_nonneg hε0 (by norm_num))
  have ha : 0 < 1 - 2 * (-(ε / 4)) := by linarith
  have hlog := sub_sq_le_log_one_add (u := ε / 2)
    (div_nonneg hε0 (by norm_num))
  calc
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
      {ω | (∑ i, (ω i) ^ 2) ≤ (d : ℝ) * (1 - ε)} ≤
      Real.exp (-(-(ε / 4)) * ((d : ℝ) * (1 - ε))) *
        (Real.sqrt (1 - 2 * (-(ε / 4))))⁻¹ ^ d :=
      sum_sq_pi_lower_chernoff d ε (-(ε / 4)) ht
    _ = Real.exp (-(-(ε / 4)) * ((d : ℝ) * (1 - ε)) -
      ((d : ℝ) / 2) * Real.log (1 + ε / 2)) := by
      rw [sqrt_inv_pow_eq_exp d ha, ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ Real.exp (-((d : ℝ) * ε ^ 2 / 8)) := by
      apply Real.exp_le_exp.mpr
      have hd : 0 ≤ (d : ℝ) := by positivity
      nlinarith
section ProjectionRows

/--
[stdGaussian_unit_projection_law](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma stdGaussian_unit_projection_law
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (anchor : E) (hAnchorNorm : ‖anchor‖ = 1) :
  (stdGaussian E).map (innerSL ℝ anchor) = gaussianReal 0 1 := by
  have hMean :
    ∫ sample, (innerSL ℝ anchor) sample ∂stdGaussian E = 0 := by
    simpa using
      (integral_strongDual_stdGaussian (L := innerSL ℝ anchor))
  have hVar :
    Var[fun sample => (innerSL ℝ anchor) sample; stdGaussian E].toNNReal =
      1 := by
    have hVarReal :
      Var[fun sample => (innerSL ℝ anchor) sample; stdGaussian E] =
        1 := by
      calc
        Var[fun sample => (innerSL ℝ anchor) sample; stdGaussian E]
          = ‖innerSL ℝ anchor‖ ^ 2 :=
          variance_dual_stdGaussian (L := innerSL ℝ anchor)
        _ = 1 := by
          simp [innerSL_apply_norm, hAnchorNorm]
    rw [hVarReal]
    norm_num
  rw [IsGaussian.map_eq_gaussianReal
    (μ := stdGaussian E)
    (L := innerSL ℝ anchor)]
  rw [hMean, hVar]

/--
[rowProjection_law](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma rowProjection_law
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) (anchor : E) (hAnchorNorm : ‖anchor‖ = 1) :
  (Measure.pi fun _ : Fin d => stdGaussian E).map (rowProjection d anchor) =
    Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  unfold rowProjection
  rw [Measure.pi_map_pi (fun _ => (innerSL ℝ anchor).measurable.aemeasurable)]
  congr 1
  funext i
  exact stdGaussian_unit_projection_law anchor hAnchorNorm

/--
[rowProjection_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma rowProjection_upper_tail
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) (anchor : E) (hAnchorNorm : ‖anchor‖ = 1)
  {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
  (Measure.pi fun _ : Fin d => stdGaussian E).real
    {rows | (d : ℝ) * (1 + ε) ≤
      ∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2} ≤
    Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
  have hm : Measurable (rowProjection d anchor) := by
    unfold rowProjection
    fun_prop
  have hLaw : HasLaw (rowProjection d anchor)
    (Measure.pi fun _ : Fin d => gaussianReal 0 1)
    (Measure.pi fun _ : Fin d => stdGaussian E) :=
    ⟨hm.aemeasurable, rowProjection_law d anchor hAnchorNorm⟩
  have heq := hLaw.measureReal_eq
    (p := fun coords : Fin d → ℝ =>
      (d : ℝ) * (1 + ε) ≤ ∑ i, (coords i) ^ 2)
    (measurableSet_le measurable_const (by fun_prop))
  change (Measure.pi fun _ : Fin d => stdGaussian E).real
    {rows | (d : ℝ) * (1 + ε) ≤
      ∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2} =
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
      {coords | (d : ℝ) * (1 + ε) ≤ ∑ i, (coords i) ^ 2} at heq
  rw [heq]
  exact sum_sq_pi_upper_tail d hε0 hε1

/--
[rowProjection_lower_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma rowProjection_lower_tail
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) (anchor : E) (hAnchorNorm : ‖anchor‖ = 1)
  {ε : ℝ} (hε0 : 0 ≤ ε) :
  (Measure.pi fun _ : Fin d => stdGaussian E).real
    {rows | (∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2) ≤
      (d : ℝ) * (1 - ε)} ≤
    Real.exp (-((d : ℝ) * ε ^ 2 / 8)) := by
  have hm : Measurable (rowProjection d anchor) := by
    unfold rowProjection
    fun_prop
  have hLaw : HasLaw (rowProjection d anchor)
    (Measure.pi fun _ : Fin d => gaussianReal 0 1)
    (Measure.pi fun _ : Fin d => stdGaussian E) :=
    ⟨hm.aemeasurable, rowProjection_law d anchor hAnchorNorm⟩
  have heq := hLaw.measureReal_eq
    (p := fun coords : Fin d → ℝ =>
      (∑ i, (coords i) ^ 2) ≤ (d : ℝ) * (1 - ε))
    (measurableSet_le (by fun_prop) measurable_const)
  change (Measure.pi fun _ : Fin d => stdGaussian E).real
    {rows | (∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2) ≤
      (d : ℝ) * (1 - ε)} =
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real
      {coords | (∑ i, (coords i) ^ 2) ≤ (d : ℝ) * (1 - ε)} at heq
  rw [heq]
  exact sum_sq_pi_lower_tail d hε0

/--
[projectionFailure_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma projectionFailure_measurable
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) (ε : ℝ) (anchor : E) :
  MeasurableSet (projectionFailure d ε anchor) := by
  apply MeasurableSet.union
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_le measurable_const (by fun_prop)

/--
[projectionFailure_real_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma projectionFailure_real_le
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) (anchor : E) (hAnchorNorm : ‖anchor‖ = 1)
  {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
  (Measure.pi fun _ : Fin d => stdGaussian E).real
    (projectionFailure d ε anchor) ≤
    2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
  calc
    (Measure.pi fun _ : Fin d => stdGaussian E).real
      (projectionFailure d ε anchor) ≤
      (Measure.pi fun _ : Fin d => stdGaussian E).real
        {rows | (∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2) ≤
          (d : ℝ) * (1 - ε)} +
      (Measure.pi fun _ : Fin d => stdGaussian E).real
        {rows | (d : ℝ) * (1 + ε) ≤
          ∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-((d : ℝ) * ε ^ 2 / 8)) +
      Real.exp (-((d : ℝ) * ε ^ 2 / 16)) :=
      add_le_add (rowProjection_lower_tail d anchor hAnchorNorm hε0)
        (rowProjection_upper_tail d anchor hAnchorNorm hε0 hε1)
    _ ≤ 2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
      have hd : 0 ≤ (d : ℝ) := by positivity
      have he : 0 ≤ ε ^ 2 := sq_nonneg ε
      have hExp : Real.exp (-((d : ℝ) * ε ^ 2 / 8)) ≤
        Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      nlinarith

/--
[pairFailure_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma pairFailure_measurable
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) (ε : ℝ) (x y : E) :
  MeasurableSet (pairFailure d ε x y) := by
  by_cases h : x = y
  · simp [pairFailure, h]
  · simp only [pairFailure, h, ↓reduceIte]
    exact projectionFailure_measurable d ε _

/--
[pairFailure_real_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma pairFailure_real_le
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x y : E) :
  (Measure.pi fun _ : Fin d => stdGaussian E).real
    (pairFailure d ε x y) ≤
    2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
  by_cases h : x = y
  · simp only [pairFailure, h, ↓reduceIte, measureReal_empty, Nat.ofNat_pos,
    mul_nonneg_iff_of_pos_left]
    positivity
  · simp only [pairFailure, h, ↓reduceIte]
    apply projectionFailure_real_le d _ _ hε0 hε1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))

/--
[anyPairFailure_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma anyPairFailure_measurable
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) (ε : ℝ) (X : Finset E) :
  MeasurableSet (anyPairFailure d ε X) := by
  unfold anyPairFailure
  exact X.measurableSet_biUnion fun x _hx =>
    X.measurableSet_biUnion fun y _hy => pairFailure_measurable d ε x y

/--
[anyPairFailure_real_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma anyPairFailure_real_le
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (X : Finset E) :
  (Measure.pi fun _ : Fin d => stdGaussian E).real
    (anyPairFailure d ε X) ≤
    (X.card : ℝ) ^ 2 *
      (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) := by
  unfold anyPairFailure
  calc
    (Measure.pi fun _ : Fin d => stdGaussian E).real
      (⋃ x ∈ X, ⋃ y ∈ X, pairFailure d ε x y) ≤
      ∑ x ∈ X, (Measure.pi fun _ : Fin d => stdGaussian E).real
        (⋃ y ∈ X, pairFailure d ε x y) :=
      measureReal_biUnion_finset_le X _
    _ ≤ ∑ x ∈ X, ∑ y ∈ X,
      (Measure.pi fun _ : Fin d => stdGaussian E).real
        (pairFailure d ε x y) := by
      gcongr with x hx
      exact measureReal_biUnion_finset_le X _
    _ ≤ ∑ _x ∈ X, ∑ _y ∈ X,
      2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by
      gcongr with x hx y hy
      exact pairFailure_real_le d hε0 hε1 x y
    _ = (X.card : ℝ) ^ 2 *
      (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) := by
      simp
      ring

/--
[exists_rows_not_anyPairFailure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma exists_rows_not_anyPairFailure
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (X : Finset E)
  (hbound : (X.card : ℝ) ^ 2 *
    (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) < 1) :
  ∃ rows : Fin d → E, rows ∉ anyPairFailure d ε X := by
  by_contra h
  push Not at h
  have hset : anyPairFailure d ε X = Set.univ := Set.eq_univ_of_forall h
  have hle := anyPairFailure_real_le d hε0 hε1 X
  rw [hset] at hle
  have hone : (Measure.pi fun _ : Fin d => stdGaussian E).real Set.univ = 1 := by simp
  rw [hone] at hle
  linarith

/--
[dimension_implies_failure_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma dimension_implies_failure_bound {N d : ℕ} {ε : ℝ}
  (hN : N ≥ 2) (hε : ε > 0)
  (hd : (d : ℝ) > 64 * ε⁻¹ ^ 2 * Real.log (N : ℝ)) :
  (N : ℝ) ^ 2 * (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) < 1 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hmul := mul_lt_mul_of_pos_right hd (show 0 < ε ^ 2 / 16 by positivity)
  have hexponent : 4 * Real.log (N : ℝ) < (d : ℝ) * ε ^ 2 / 16 := by
    calc
      4 * Real.log (N : ℝ) =
        (64 * ε⁻¹ ^ 2 * Real.log (N : ℝ)) * (ε ^ 2 / 16) := by
        field_simp
        ring
      _ < (d : ℝ) * (ε ^ 2 / 16) := hmul
      _ = (d : ℝ) * ε ^ 2 / 16 := by ring
  have hexp : Real.exp (-((d : ℝ) * ε ^ 2 / 16)) <
    ((N : ℝ)⁻¹) ^ 4 := by
    calc
      Real.exp (-((d : ℝ) * ε ^ 2 / 16)) <
        Real.exp (-(4 * Real.log (N : ℝ))) := by
        apply Real.exp_lt_exp.mpr
        linarith
      _ = Real.exp (-Real.log (N : ℝ)) ^ 4 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ = ((N : ℝ)⁻¹) ^ 4 := by rw [Real.exp_neg, Real.exp_log hNreal]
  have hcoef : 0 < (N : ℝ) ^ 2 * 2 := by positivity
  have hmulExp := mul_lt_mul_of_pos_left hexp hcoef
  calc
    (N : ℝ) ^ 2 * (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) =
      ((N : ℝ) ^ 2 * 2) * Real.exp (-((d : ℝ) * ε ^ 2 / 16)) := by ring
    _ < ((N : ℝ) ^ 2 * 2) * ((N : ℝ)⁻¹) ^ 4 := hmulExp
    _ ≤ 1 := by
      have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      field_simp
      nlinarith

/--
[gaussianMap_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma gaussianMap_sub
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (d : ℕ) (rows : Fin d → E) (x y : E) :
  gaussianMap d rows x - gaussianMap d rows y =
    WithLp.toLp 2 (fun i => (Real.sqrt (d : ℝ))⁻¹ *
      (innerSL ℝ (x - y)) (rows i)) := by
  ext i
  simp [gaussianMap]
  ring

/--
[gaussianMap_norm_sq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma gaussianMap_norm_sq_sub
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (d : ℕ) (hd : 0 < d) (rows : Fin d → E) (x y : E) :
  ‖gaussianMap d rows x - gaussianMap d rows y‖ ^ 2 =
    ((d : ℝ)⁻¹) * ∑ i, ((innerSL ℝ (x - y)) (rows i)) ^ 2 := by
  rw [gaussianMap_sub, EuclideanSpace.real_norm_sq_eq]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  congr 1
  rw [inv_pow, Real.sq_sqrt hdreal.le]

/--
[sum_inner_sq_eq_norm_sq_mul_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma sum_inner_sq_eq_norm_sq_mul_normalized
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (d : ℕ) (rows : Fin d → E) {z : E} (hz : z ≠ 0) :
  (∑ i, ((innerSL ℝ z) (rows i)) ^ 2) =
    ‖z‖ ^ 2 *
      ∑ i, ((innerSL ℝ (‖z‖⁻¹ • z)) (rows i)) ^ 2 := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  calc
    (∑ i, ((innerSL ℝ z) (rows i)) ^ 2) =
      ∑ i, (‖z‖ * ((innerSL ℝ (‖z‖⁻¹ • z)) (rows i))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      congr 1
      simp only [innerSL_apply_apply, real_inner_smul_left]
      field_simp
    _ = ‖z‖ ^ 2 *
      ∑ i, ((innerSL ℝ (‖z‖⁻¹ • z)) (rows i)) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]

/--
[gaussianMap_pair_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
private lemma gaussianMap_pair_bounds
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (d : ℕ) (hd : 0 < d) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
  (rows : Fin d → E) (x y : E)
  (hgood : rows ∉ pairFailure d ε x y) :
  (1 - ε) * ‖x - y‖ ≤ ‖gaussianMap d rows x - gaussianMap d rows y‖ ∧
    ‖gaussianMap d rows x - gaussianMap d rows y‖ ≤ (1 + ε) * ‖x - y‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  · have hgood' : rows ∉
    projectionFailure d ε (‖x - y‖⁻¹ • (x - y)) := by
    simpa [pairFailure, hxy] using hgood
    have htails :
      ¬((∑ i, ((innerSL ℝ (‖x - y‖⁻¹ • (x - y))) (rows i)) ^ 2) ≤
        (d : ℝ) * (1 - ε)) ∧
      ¬((d : ℝ) * (1 + ε) ≤
        ∑ i, ((innerSL ℝ (‖x - y‖⁻¹ • (x - y))) (rows i)) ^ 2) := by
      simpa [projectionFailure] using hgood'
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    let S : ℝ := ∑ i, ((innerSL ℝ (‖x - y‖⁻¹ • (x - y))) (rows i)) ^ 2
    have hSlower : 1 - ε < (d : ℝ)⁻¹ * S := by
      have h := lt_of_not_ge htails.1
      change (d : ℝ) * (1 - ε) < S at h
      have hm := mul_lt_mul_of_pos_left h (inv_pos.mpr hdreal)
      have hinv : (d : ℝ)⁻¹ * (d : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hdreal)
      nlinarith
    have hSupper : (d : ℝ)⁻¹ * S < 1 + ε := by
      have h := lt_of_not_ge htails.2
      change S < (d : ℝ) * (1 + ε) at h
      have hm := mul_lt_mul_of_pos_left h (inv_pos.mpr hdreal)
      have hinv : (d : ℝ)⁻¹ * (d : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hdreal)
      nlinarith
    have hnormsq : ‖gaussianMap d rows x - gaussianMap d rows y‖ ^ 2 =
      ‖x - y‖ ^ 2 * ((d : ℝ)⁻¹ * S) := by
      rw [gaussianMap_norm_sq_sub d hd rows x y,
        sum_inner_sq_eq_norm_sq_mul_normalized d rows (sub_ne_zero.mpr hxy)]
      ring
    have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hlowerSq : ((1 - ε) * ‖x - y‖) ^ 2 ≤
      ‖gaussianMap d rows x - gaussianMap d rows y‖ ^ 2 := by
      rw [hnormsq]
      have hm := mul_lt_mul_of_pos_left hSlower (sq_pos_of_pos hr)
      nlinarith
    have hupperSq : ‖gaussianMap d rows x - gaussianMap d rows y‖ ^ 2 ≤
      ((1 + ε) * ‖x - y‖) ^ 2 := by
      rw [hnormsq]
      have hm := mul_lt_mul_of_pos_left hSupper (sq_pos_of_pos hr)
      nlinarith
    constructor
    · have hlower0 : 0 ≤ (1 - ε) * ‖x - y‖ := mul_nonneg (sub_nonneg.mpr hε1) (norm_nonneg _)
      nlinarith [norm_nonneg (gaussianMap d rows x - gaussianMap d rows y)]
    · have hupper0 : 0 ≤ (1 + ε) * ‖x - y‖ :=
      mul_nonneg (by linarith) (norm_nonneg _)
      nlinarith [norm_nonneg (gaussianMap d rows x - gaussianMap d rows y)]
end ProjectionRows
section

namespace MathlibExt.Geometry.Euclidean.JohnsonLindenstraussWanted

/--
[johnson_lindenstrauss](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean)
-/
@[path]
lemma johnson_lindenstrauss
  :
-- imply
  ∃ C : ℝ, C > 0 ∧
    ∀ (ε : ℝ), ε > 0 →
    ∀ (m : ℕ) (N : ℕ), N ≥ 2 →
    ∀ (X : Finset (EuclideanSpace ℝ (Fin m))), X.card = N →
    ∀ (d : ℕ), (d : ℝ) > C * ε⁻¹ ^ 2 * Real.log (N : ℝ) →
    ∃ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d),
    ∀ x ∈ X, ∀ y ∈ X,
    (1 - ε) * ‖x - y‖ ≤ ‖f x - f y‖ ∧
    ‖f x - f y‖ ≤ (1 + ε) * ‖x - y‖ := by
-- proof
  refine ⟨64, by norm_num, ?_⟩
  intro ε hε m N hN X hcard d hd
  by_cases hε1 : ε ≤ 1
  · have hlog : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
    have hdreal : 0 < (d : ℝ) := by
      have hright : 0 < 64 * ε⁻¹ ^ 2 * Real.log (N : ℝ) := by positivity
      linarith
    have hdpos : 0 < d := by exact_mod_cast hdreal
    have hbound : (X.card : ℝ) ^ 2 *
      (2 * Real.exp (-((d : ℝ) * ε ^ 2 / 16))) < 1 := by
      rw [hcard]
      exact dimension_implies_failure_bound hN hε hd
    obtain ⟨rows, hrows⟩ :=
      exists_rows_not_anyPairFailure d hε.le hε1 X hbound
    refine ⟨gaussianMap d rows, ?_⟩
    intro x hx y hy
    apply gaussianMap_pair_bounds d hdpos hε.le hε1 rows x y
    intro hpair
    apply hrows
    unfold anyPairFailure
    exact Set.mem_iUnion_of_mem x <| Set.mem_iUnion_of_mem hx <|
      Set.mem_iUnion_of_mem y <| Set.mem_iUnion_of_mem hy hpair
  · have hεge : 1 ≤ ε := le_of_not_ge hε1
    refine ⟨fun _ => 0, ?_⟩
    intro x hx y hy
    simp only [sub_self, norm_zero]
    constructor
    · have : (1 - ε) * ‖x - y‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hεge) (norm_nonneg _)
      simpa using this
    · exact mul_nonneg (by linarith) (norm_nonneg _)

end MathlibExt.Geometry.Euclidean.JohnsonLindenstraussWanted


-- created on 2026-10-20
-- updated on 2026-10-23
