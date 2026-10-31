import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Algebra.BigOperators.Fin
import Def.Probability.ChiSquare
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal


private lemma eq_of_mgf_id
  {μ ν : Measure ℝ}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (h_mgf : mgf id μ = mgf id ν)
  (h0 : 0 ∈ interior (integrableExpSet id μ)) :
  μ = ν := by
  have hstrip := eqOn_complexMGF_of_mgf (X := (id : ℝ → ℝ)) (μ := μ)
    (Y := (id : ℝ → ℝ)) (μ' := ν) h_mgf
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  have ht : ((t : ℂ) * Complex.I).re ∈ interior (integrableExpSet (id : ℝ → ℝ) μ) := by
    simpa using h0
  simpa [complexMGF_id_mul_I] using hstrip ht

private lemma mgf_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
  mgf id (gammaMeasure a r) t = (r / (r - t)) ^ a := by
  have hr_t : 0 < r - t := sub_pos.mpr ht
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  simp only [mgf, id_eq, gammaMeasure]
  have hmeas : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  have hlt : ∀ᵐ x ∂volume, gammaPDF a r x < ∞ := ae_of_all _ fun _ ↦ by simp [gammaPDF]
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  simp_rw [smul_eq_mul]
  have hto : ∀ x, (gammaPDF a r x).toReal = gammaPDFReal a r x := fun x ↦
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)
  simp_rw [hto]
  have hfull :
    ∫ x, gammaPDFReal a r x * rexp (t * x) =
      ∫ x in Ici (0 : ℝ), gammaPDFReal a r x * rexp (t * x) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    have : x < 0 := lt_of_not_ge (by simpa [mem_Ici] using hx)
    simp [gammaPDFReal, not_le.mpr this]
  rw [hfull, integral_Ici_eq_integral_Ioi]
  have hpos :
    ∀ x ∈ Ioi (0 : ℝ),
      gammaPDFReal a r x * rexp (t * x) =
        r ^ a / Gamma a * (x ^ (a - 1) * rexp (-((r - t) * x))) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    simp only [gammaPDFReal, ite_eq_left hx0]
    rw [mul_assoc, mul_assoc, ← exp_add]
    congr 3
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpos, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_Ioi ha hr_t]
  have hG : Gamma a ≠ 0 := (Gamma_pos_of_pos ha).ne'
  calc
    _ = r ^ a / Gamma a * ((1 / (r - t)) ^ a * Gamma a) := rfl
    _ = r ^ a * (1 / (r - t)) ^ a := by field_simp [hG]
    _ = (r / (r - t)) ^ a := by
      rw [← mul_rpow hr.le (one_div_nonneg.mpr hr_t.le), ← div_eq_mul_one_div]

private lemma integrable_exp_mul_of_lt_rate {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
  Integrable (fun x ↦ rexp (t * x)) (gammaMeasure a r) := by
  have : NeZero (gammaMeasure a r) :=
    ⟨(isProbabilityMeasure_gammaMeasure ha hr).ne_zero⟩
  refine (mgf_pos_iff (μ := gammaMeasure a r)).mp ?_
  change 0 < mgf id (gammaMeasure a r) t
  rw [mgf_id_gammaMeasure ha hr ht]
  positivity

private lemma zero_mem_interior_integrableExpSet_gammaMeasure
  {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
  0 ∈ interior (integrableExpSet id (gammaMeasure a r)) := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  refine mem_interior.mpr ⟨Ioo (-(r / 2)) (r / 2), ?_, isOpen_Ioo, by constructor <;> linarith⟩
  intro t ht
  simp only [integrableExpSet, mem_ofPred_eq, id_eq]
  exact integrable_exp_mul_of_lt_rate ha hr (by linarith [ht.2])

private lemma mgf_id_map_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
  mgf id ((gaussianReal 0 1).map fun x ↦ x ^ 2) t =
    (1 - 2 * t) ^ (-(1 / 2 : ℝ)) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hb : 0 < (1 / 2 - (t : ℝ)) := by linarith
  have hme : AEMeasurable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by fun_prop
  rw [mgf_id_map hme]
  simp only [mgf]
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hintegrand :
    (fun x : ℝ ↦ gaussianPDFReal 0 1 x * rexp (t * x ^ 2)) =
      fun x ↦ (√(2 * π))⁻¹ * rexp (-(1 / 2 - t) * x ^ 2) := by
    funext x
    simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
    rw [mul_assoc, ← exp_add]
    refine congr_arg₂ (fun a b ↦ a * b) ?_ (congr_arg rexp ?_)
    · ring_nf
    · ring
  rw [hintegrand, integral_const_mul, integral_gaussian]
  have h2π : 0 < 2 * π := by positivity
  have hden : 0 < 1 - 2 * t := by linarith
  have hhalf : 0 ≤ 1 / 2 - t := hb.le
  calc
    _ = (√(2 * π))⁻¹ * √(π / (1 / 2 - t)) := rfl
    _ = √((2 * π)⁻¹) * √(π / (1 / 2 - t)) := by rw [sqrt_inv]
    _ = √((2 * π)⁻¹ * (π / (1 / 2 - t))) := by
      rw [← sqrt_mul (inv_nonneg.mpr h2π.le)]
    _ = √(1 / (2 * (1 / 2 - t))) := by
      congr 1
      field_simp
    _ = √(1 / (1 - 2 * t)) := by
      congr 1
      ring
    _ = (1 - 2 * t) ^ (-(1 / 2 : ℝ)) := by
      rw [sqrt_eq_rpow, one_div, inv_rpow hden.le, ← rpow_neg hden.le]

private lemma not_integrable_exp_mul_map_sq {t : ℝ} (ht : (1 / 2 : ℝ) ≤ t) :
  ¬Integrable (fun x ↦ rexp (t * x)) ((gaussianReal 0 1).map fun x ↦ x ^ 2) := by
  intro h
  have hASM : AEStronglyMeasurable (fun x : ℝ ↦ rexp (t * x))
    ((gaussianReal 0 1).map fun x ↦ x ^ 2) := by fun_prop
  have hAM : AEMeasurable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) := by fun_prop
  have h' : Integrable (fun x : ℝ ↦ rexp (t * x ^ 2)) (gaussianReal 0 1) :=
    (integrable_map_measure (f := fun x : ℝ ↦ x ^ 2) (g := fun x : ℝ ↦ rexp (t * x))
      hASM hAM).1 h
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero _ hv] at h'
  have hmeas := measurable_gaussianPDF (0 : ℝ) 1
  have hlt : ∀ᵐ x ∂volume, gaussianPDF 0 1 x < ∞ := ae_of_all _ fun _ ↦ by simp [gaussianPDF]
  rw [integrable_withDensity_iff hmeas hlt] at h'
  have hto : ∀ x, (gaussianPDF 0 1 x).toReal = gaussianPDFReal 0 1 x := fun x ↦
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)
  simp_rw [hto] at h'
  have heq :
    (fun x ↦ rexp (t * x ^ 2) * gaussianPDFReal 0 1 x) =
      fun x ↦ (√(2 * π))⁻¹ * rexp (-(1 / 2 - t) * x ^ 2) := by
    funext x
    simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
    rw [mul_comm (rexp _), mul_assoc, ← exp_add]
    refine congr_arg₂ (fun a b ↦ a * b) ?_ (congr_arg rexp ?_)
    · ring_nf
    · ring
  rw [heq] at h'
  have hc : IsUnit ((√(2 * π) : ℝ)⁻¹) := isUnit_iff_ne_zero.mpr (by positivity)
  have hbase : Integrable (fun x ↦ rexp (-(1 / 2 - t) * x ^ 2)) :=
    (integrable_const_mul_iff (μ := volume) hc _).1 h'
  have : ¬Integrable (fun x ↦ rexp (-(1 / 2 - t) * x ^ 2)) := by
    rw [integrable_exp_neg_mul_sq_iff]
    linarith
  exact this hbase

private lemma not_integrable_exp_mul_gammaMeasure_at_rate {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
  ¬Integrable (fun x ↦ rexp (r * x)) (gammaMeasure a r) := by
  intro h
  have hmeas : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  have hlt : ∀ᵐ x ∂volume, gammaPDF a r x < ∞ := ae_of_all _ fun _ ↦ by simp [gammaPDF]
  rw [gammaMeasure, integrable_withDensity_iff hmeas hlt] at h
  have hto : ∀ x, (gammaPDF a r x).toReal = gammaPDFReal a r x := fun x ↦
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)
  simp_rw [hto] at h
  have hOn : IntegrableOn (fun x ↦ rexp (r * x) * gammaPDFReal a r x) (Ioi (0 : ℝ)) :=
    h.integrableOn
  have heq :
    ∀ x ∈ Ioi (0 : ℝ),
      rexp (r * x) * gammaPDFReal a r x = r ^ a / Gamma a * x ^ (a - 1) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    simp only [gammaPDFReal, ite_eq_left hx0]
    rw [mul_comm (rexp _), mul_assoc, mul_assoc, ← exp_add]
    have hcancel : -(r * x) + r * x = 0 := by ring
    rw [hcancel, exp_zero, mul_one]
  have hOn' : IntegrableOn (fun x ↦ r ^ a / Gamma a * x ^ (a - 1)) (Ioi (0 : ℝ)) :=
    hOn.congr_fun heq measurableSet_Ioi
  have hc : IsUnit (r ^ a / Gamma a) :=
    isUnit_iff_ne_zero.mpr (div_ne_zero (by positivity) (Gamma_pos_of_pos ha).ne')
  have : IntegrableOn (fun x ↦ x ^ (a - 1)) (Ioi (0 : ℝ)) :=
    (integrable_const_mul_iff (μ := volume.restrict (Ioi (0 : ℝ))) hc _).1 hOn'
  exact not_integrableOn_Ioi_rpow (a - 1) this

private lemma not_integrable_exp_mul_gammaMeasure_of_ge_rate
  {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : r ≤ t) :
  ¬Integrable (fun x ↦ rexp (t * x)) (gammaMeasure a r) := by
  intro h
  have hmeas : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  have hlt : ∀ᵐ x ∂volume, gammaPDF a r x < ∞ := ae_of_all _ fun _ ↦ by simp [gammaPDF]
  refine not_integrable_exp_mul_gammaMeasure_at_rate ha hr ?_
  rw [gammaMeasure, integrable_withDensity_iff hmeas hlt] at h ⊢
  have hto : ∀ x, (gammaPDF a r x).toReal = gammaPDFReal a r x := fun x ↦
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)
  simp_rw [hto] at h ⊢
  refine Integrable.mono_nonneg h (by fun_prop) ?_ ?_
  · exact ae_of_all _ fun x ↦
      mul_nonneg (exp_pos _).le (gammaPDFReal_nonneg ha hr x)
  ·
    refine ae_of_all _ fun x ↦ ?_
    if hx : 0 ≤ x then
      exact mul_le_mul_of_nonneg_right
        (exp_monotone (mul_le_mul_of_nonneg_right ht hx))
        (gammaPDFReal_nonneg ha hr x)
    else
      simp [gammaPDFReal, not_le.mpr (lt_of_not_ge hx)]

private lemma map_sq_gaussianReal_eq_gammaMeasure :
  (gaussianReal 0 1).map (fun x ↦ x ^ 2) = gammaMeasure (1 / 2) (1 / 2) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hμ : IsProbabilityMeasure ((gaussianReal 0 1).map fun x ↦ x ^ 2) := inferInstance
  have : IsProbabilityMeasure (gammaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure ha hr
  refine eq_of_mgf_id ?_ ?_
  ·
    ext t
    if ht : t < 1 / 2 then
      rw [mgf_id_map_sq_gaussianReal ht, mgf_id_gammaMeasure ha hr ht]
      refine Eq.symm ?_
      have hden' : 0 < 1 - 2 * t := by linarith
      calc
        _ = ((1 / 2) / (1 / 2 - t)) ^ (1 / 2 : ℝ) := rfl
        _ = (1 / (2 * (1 / 2 - t))) ^ (1 / 2 : ℝ) := by
          congr 1
          field_simp
        _ = (1 / (1 - 2 * t)) ^ (1 / 2 : ℝ) := by
          congr 1
          ring
        _ = (1 - 2 * t) ^ (-(1 / 2 : ℝ)) := by
          rw [one_div, inv_rpow hden'.le, ← rpow_neg hden'.le]
    else
      have ht' : (1 / 2 : ℝ) ≤ t := le_of_not_gt ht
      rw [mgf_undef (X := (id : ℝ → ℝ)) (not_integrable_exp_mul_map_sq ht'),
        mgf_undef (X := (id : ℝ → ℝ))
          (not_integrable_exp_mul_gammaMeasure_of_ge_rate ha hr ht')]
  ·
    refine mem_interior.mpr ⟨Ioo (-(1 / 4 : ℝ)) (1 / 4), ?_, isOpen_Ioo, by constructor <;> norm_num⟩
    intro s hs
    simp only [integrableExpSet, mem_ofPred_eq, id_eq]
    have hs' : s < 1 / 2 := by linarith [hs.2]
    have hpos : 0 < mgf id ((gaussianReal 0 1).map fun x ↦ x ^ 2) s := by
      rw [mgf_id_map_sq_gaussianReal hs']
      have : 0 < 1 - 2 * s := by linarith [hs.2]
      positivity
    have : NeZero ((gaussianReal 0 1).map fun x ↦ x ^ 2) := ⟨hμ.ne_zero⟩
    exact (mgf_pos_iff).mp hpos

private lemma mgf_id_conv
  (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ) :
  mgf id (μ ∗ ν) t = mgf id μ t * mgf id ν t := by
  have hme : AEMeasurable (fun p : ℝ × ℝ ↦ p.1 + p.2) (μ.prod ν) := by fun_prop
  change mgf id ((μ.prod ν).map fun p ↦ p.1 + p.2) t = _
  rw [mgf_id_map hme]
  have hindep : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd (μ.prod ν) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable]
    simp [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ,
      show (fun ω : ℝ × ℝ ↦ (ω.1, ω.2)) = id by ext <;> rfl, Measure.map_id]
  have hadd :=
    hindep.mgf_add' measurable_fst.aestronglyMeasurable
      measurable_snd.aestronglyMeasurable (t := t)
  have hsum : (Prod.fst + Prod.snd : ℝ × ℝ → ℝ) = fun p ↦ p.1 + p.2 := by
    ext p; simp [Pi.add_apply]
  rw [← hsum, hadd]
  congr 1
  ·
    have : mgf Prod.fst (μ.prod ν) = mgf id μ := by
      rw [← mgf_id_map measurable_fst.aemeasurable, Measure.map_fst_prod, measure_univ,
        one_smul]
    exact congrFun this t
  ·
    have : mgf Prod.snd (μ.prod ν) = mgf id ν := by
      rw [← mgf_id_map measurable_snd.aemeasurable, Measure.map_snd_prod, measure_univ,
        one_smul]
    exact congrFun this t

private lemma gammaMeasure_conv {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
  gammaMeasure a r ∗ gammaMeasure b r = gammaMeasure (a + b) r := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  have : IsProbabilityMeasure (gammaMeasure b r) := isProbabilityMeasure_gammaMeasure hb hr
  have hab : 0 < a + b := by positivity
  have : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
    isProbabilityMeasure_gammaMeasure hab hr
  refine (eq_of_mgf_id (μ := gammaMeasure (a + b) r)
      (ν := gammaMeasure a r ∗ gammaMeasure b r) ?_
      (zero_mem_interior_integrableExpSet_gammaMeasure hab hr)).symm
  ext t
  if ht : t < r then
    rw [mgf_id_gammaMeasure hab hr ht, mgf_id_conv, mgf_id_gammaMeasure ha hr ht,
      mgf_id_gammaMeasure hb hr ht]
    exact rpow_add (div_pos hr (sub_pos.mpr ht)) a b
  else
    have ht' : r ≤ t := le_of_not_gt ht
    rw [mgf_undef (X := (id : ℝ → ℝ))
        (not_integrable_exp_mul_gammaMeasure_of_ge_rate hab hr ht'),
      mgf_id_conv,
      mgf_undef (X := (id : ℝ → ℝ))
        (not_integrable_exp_mul_gammaMeasure_of_ge_rate ha hr ht')]
    ring

private lemma sum_sq_snoc {n : ℕ} (x : Fin n → ℝ) (y : ℝ) :
  (∑ i : Fin (n + 1), (@Fin.snoc n (fun _ ↦ ℝ) x y i) ^ 2) =
    (∑ i, x i ^ 2) + y ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

private lemma sumSqGaussians_succ (n : ℕ) :
  sumSqGaussians (n + 1) =
    sumSqGaussians n ∗ ((gaussianReal 0 1).map fun x ↦ x ^ 2) := by
  let μ : Fin (n + 1) → Measure ℝ := fun _ ↦ gaussianReal 0 1
  have hmp := (measurePreserving_piFinSuccAbove μ (Fin.last n)).symm
  have hπ :
    Measure.pi μ =
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1)).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).symm :=
    hmp.map_eq.symm
  unfold sumSqGaussians
  have hsum_meas :
    Measurable (fun x : Fin (n + 1) → ℝ ↦ ∑ i, x i ^ 2) := by fun_prop
  have hequiv_meas :
    Measurable
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).symm :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).symm.measurable
  rw [hπ, Measure.map_map hsum_meas hequiv_meas]
  have hcomp :
    ((fun x : Fin (n + 1) → ℝ ↦ ∑ i, x i ^ 2) ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).symm) =
      fun p : ℝ × (Fin n → ℝ) ↦ p.1 ^ 2 + ∑ i, p.2 i ^ 2 := by
    funext p
    simp only [Function.comp_apply]
    have hins :
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).symm p =
        @Fin.insertNth n (fun _ ↦ ℝ) (Fin.last n) p.1 p.2 := rfl
    rw [hins, @Fin.insertNth_last' n ℝ p.1 p.2, sum_sq_snoc p.2 p.1, add_comm]
  rw [hcomp]
  have hf : Measurable (fun x : ℝ ↦ x ^ 2) := by fun_prop
  have hg : Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2) := by fun_prop
  have hadd : Measurable (fun q : ℝ × ℝ ↦ q.1 + q.2) := by fun_prop
  have hprodmap :
    Measurable
      (Prod.map (fun x : ℝ ↦ x ^ 2) (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2)) :=
    hf.prodMap hg
  have hEq :
    (fun p : ℝ × (Fin n → ℝ) ↦ p.1 ^ 2 + ∑ i, p.2 i ^ 2) =
      (fun q : ℝ × ℝ ↦ q.1 + q.2) ∘
        Prod.map (fun x ↦ x ^ 2) (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2) := by
    funext p; rfl
  -- map (add ∘ Prod.map f g) (μ × ν)
  --   = map add (map (Prod.map f g) (μ × ν))     [← map_map]
  --   = map add ((map f μ) × (map g ν))           [← map_prod_map]
  --   = (map f μ) ∗ (map g ν)                     [def conv]
  rw [hEq, ← Measure.map_map hadd hprodmap, ← Measure.map_prod_map _ _ hf hg]
  change ((gaussianReal 0 1).map fun x ↦ x ^ 2) ∗
      ((Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map fun x ↦ ∑ i, x i ^ 2) = _
  rw [Measure.conv_comm]

private lemma sumSqGaussians_zero : sumSqGaussians 0 = Real.chiSquare 0 := by
  unfold sumSqGaussians Real.chiSquare
  have hfun : (fun x : Fin 0 → ℝ ↦ ∑ i, (x i) ^ 2) = fun _ ↦ (0 : ℝ) := by
    funext x
    simp
  rw [hfun, Measure.pi_of_empty, Measure.map_const]
  simp [measure_univ, one_smul]

/--
Characterization: the sum-of-squares pushforward of `n` i.i.d. standard Gaussians
equals the textbook chi-squared measure `Real.chiSquare n`.
-/
@[path]
private lemma main
-- given
  (n : ℕ) :
-- imply
  (sumSqGaussians n : Measure ℝ) = Real.chiSquare n := by
-- proof
  induction n with
  | zero =>
    apply sumSqGaussians_zero
  | succ n ih =>
    rw [sumSqGaussians_succ, ih, map_sq_gaussianReal_eq_gammaMeasure]
    unfold Real.chiSquare
    if hn : n = 0 then
      subst hn
      simp only [Nat.zero_add, Nat.cast_one, one_div, one_ne_zero, ↓reduceIte]
      have ha : (0 : ℝ) < 1 / 2 := by norm_num
      have hr : (0 : ℝ) < 1 / 2 := by norm_num
      have : IsProbabilityMeasure (gammaMeasure (1 / 2 : ℝ) (1 / 2)) :=
        isProbabilityMeasure_gammaMeasure ha hr
      simpa using (Measure.dirac_zero_conv (gammaMeasure (1 / 2 : ℝ) (1 / 2)))
    else
      have hn0 : n ≠ 0 := hn
      simp only [hn0, ↓reduceIte, Nat.succ_ne_zero]
      have ha : 0 < (n : ℝ) / 2 := by
        have : (0 : ℕ) < n := Nat.pos_of_ne_zero hn0
        positivity
      have hb : (0 : ℝ) < 1 / 2 := by norm_num
      have hr : (0 : ℝ) < 1 / 2 := by norm_num
      have hconv := gammaMeasure_conv ha hb hr
      refine hconv.trans ?_
      congr 1
      push_cast
      ring


-- created on 2026-10-30
-- updated on 2026-10-31
