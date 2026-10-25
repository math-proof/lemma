import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.Parametrix.Part2
open MvPolynomial MeasureTheory ContinuousLinearMap Filter Asymptotics DifferentialOperators
open scoped SchwartzMap


namespace DifferentialOperators

/--
[cauchyRiemannDistribution_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
lemma cauchyRiemannDistribution_apply
  {φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)} :
-- imply
  cauchyRiemannDistribution φ = ∫ v : EuclideanSpace ℝ (Fin 2), φ v • cauchyRiemannKernel v :=
-- proof
  rfl

end DifferentialOperators

namespace DifferentialOperators

/--
[cauchyPompeiu_excised_ball_integral_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
lemma cauchyPompeiu_excised_ball_integral_vanishes
  {ψ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)} :
-- imply
  Tendsto (fun ε : ℝ => ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) ε, ψ v • cauchyRiemannKernel v) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
-- proof
  have hint : Integrable (fun v => ψ v • cauchyRiemannKernel v) volume :=
    cauchyRiemannKernel_schwartz_integrable ψ
  have hmeas_tendsto : Tendsto (volume ∘ fun ε => Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) ε)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Tendsto (fun r => (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (Metric.cthickening r {(0 : EuclideanSpace ℝ (Fin 2))})) (nhds 0)
      (nhds ((volume : Measure (EuclideanSpace ℝ (Fin 2)))
        {(0 : EuclideanSpace ℝ (Fin 2))})) := by
      apply tendsto_measure_cthickening_of_isClosed
      · refine ⟨1, one_pos, ?_⟩
        rw [Metric.cthickening_singleton (0 : EuclideanSpace ℝ (Fin 2))
          (by linarith : (0 : ℝ) ≤ 1)]
        exact measure_closedBall_lt_top.ne
      · exact isClosed_singleton
    rw [measure_singleton] at h1
    have h2 : Tendsto (fun r => (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (Metric.cthickening r {(0 : EuclideanSpace ℝ (Fin 2))}))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      h1.mono_left nhdsWithin_le_nhds
    refine Tendsto.congr' ?_ h2
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Function.comp_apply,
      Metric.cthickening_singleton (0 : EuclideanSpace ℝ (Fin 2)) (le_of_lt hε)]
  exact (hint.tendsto_setIntegral_nhds_zero hmeas_tendsto).mono_left le_rfl
set_option maxHeartbeats 8000000 in

end DifferentialOperators

namespace DifferentialOperators

/--
[two_eps_mul_integral_inv_eps_sq_add_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
lemma two_eps_mul_integral_inv_eps_sq_add_sq
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  2 * ε * ∫ y in (-ε)..ε, (ε ^ 2 + y ^ 2)⁻¹ = Real.pi := by
-- proof
  rw [integral_inv_sq_add_sq hε.ne']
  rw [div_self hε.ne', neg_div, div_self hε.ne']
  rw [Real.arctan_one, Real.arctan_neg, Real.arctan_one]
  field_simp
  ring

end DifferentialOperators

namespace DifferentialOperators

/--
[four_eps_mul_integral_inv_eps_sq_add_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
lemma four_eps_mul_integral_inv_eps_sq_add_sq
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  4 * ε * ∫ y in (-ε)..ε, (ε ^ 2 + y ^ 2)⁻¹ = 2 * Real.pi := by
-- proof
  rw [integral_inv_sq_add_sq hε.ne']
  rw [div_self hε.ne', neg_div, div_self hε.ne']
  rw [Real.arctan_one, Real.arctan_neg, Real.arctan_one]
  field_simp
  ring
set_option maxHeartbeats 800000 in

end DifferentialOperators

namespace DifferentialOperators

/--
[fourier_polySymbol_eq_neg_dbar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
lemma fourier_polySymbol_eq_neg_dbar
  {φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)} :
-- imply
  FourierTransform.fourier ((SchwartzMap.smulLeftCLM ℂ (polySymbol 2 dbarPoly)) (FourierTransformInv.fourierInv φ)) = -(LineDeriv.lineDerivOp (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) φ + Complex.I • LineDeriv.lineDerivOp (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) φ) := by
-- proof
  set e₀ := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  set ψ := FourierTransformInv.fourierInv φ
  have hpoly_tg : Function.HasTemperateGrowth (polySymbol 2 dbarPoly) :=
    polySymbol_hasTemperateGrowth 2 dbarPoly
  have hinner0_tg : Function.HasTemperateGrowth
    (fun x : EuclideanSpace ℝ (Fin 2) => @inner ℝ _ _ x e₀) :=
    Function.hasTemperateGrowth_inner_left e₀
  have hinner1_tg : Function.HasTemperateGrowth
    (fun x : EuclideanSpace ℝ (Fin 2) => @inner ℝ _ _ x e₁) :=
    Function.hasTemperateGrowth_inner_left e₁
  have hdecomp : (SchwartzMap.smulLeftCLM ℂ (polySymbol 2 dbarPoly)) ψ =
    (2 * ↑Real.pi * Complex.I) •
      (SchwartzMap.smulLeftCLM ℂ (fun x => @inner ℝ _ _ x e₀)) ψ +
    Complex.I • ((2 * ↑Real.pi * Complex.I) •
      (SchwartzMap.smulLeftCLM ℂ (fun x => @inner ℝ _ _ x e₁)) ψ) := by
    ext ξ
    simp only [SchwartzMap.smulLeftCLM_apply_apply hpoly_tg,
      SchwartzMap.smulLeftCLM_apply_apply hinner0_tg,
      SchwartzMap.smulLeftCLM_apply_apply hinner1_tg,
      SchwartzMap.add_apply, SchwartzMap.smul_apply]
    simp only [polySymbol, dbarPoly, eval_add, eval_mul, eval_X, eval_C]
    have h0 := EuclideanSpace.inner_single_right (ι := Fin 2) (𝕜 := ℝ) (0 : Fin 2) (1 : ℝ) ξ
    have h1 := EuclideanSpace.inner_single_right (ι := Fin 2) (𝕜 := ℝ) (1 : Fin 2) (1 : ℝ) ξ
    simp only [one_mul, starRingEnd_apply, star_trivial] at h0 h1
    simp only [show (inner ℝ ξ e₀ : ℝ) = ξ.ofLp 0 from h0,
      show (inner ℝ ξ e₁ : ℝ) = ξ.ofLp 1 from h1]
    change (2 * ↑Real.pi * Complex.I * ↑(ξ.ofLp 0) + Complex.I * (2 * ↑Real.pi * Complex.I * ↑(ξ.ofLp 1))) * ψ ξ =
      2 * ↑Real.pi * Complex.I * (↑(ξ.ofLp 0) * ψ ξ) +
        Complex.I * (2 * ↑Real.pi * Complex.I * (↑(ξ.ofLp 1) * ψ ξ))
    ring
  have h0 := SchwartzMap.lineDerivOp_fourier_eq ψ e₀
  rw [show FourierTransform.fourier ψ = φ from FourierTransform.fourier_fourierInv_eq φ] at h0
  have h1 := SchwartzMap.lineDerivOp_fourier_eq ψ e₁
  rw [show FourierTransform.fourier ψ = φ from FourierTransform.fourier_fourierInv_eq φ] at h1
  rw [hdecomp]
  ext ξ
  simp only [SchwartzMap.neg_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply]
  have four_add := FourierAdd.fourier_add
    ((2 * ↑Real.pi * Complex.I) • (SchwartzMap.smulLeftCLM ℂ (fun x => @inner ℝ _ _ x e₀)) ψ)
    (Complex.I • ((2 * ↑Real.pi * Complex.I) • (SchwartzMap.smulLeftCLM ℂ (fun x => @inner ℝ _ _ x e₁)) ψ))
  have four_add_pt := congr_fun (congrArg DFunLike.coe four_add) ξ
  simp only [SchwartzMap.add_apply] at four_add_pt
  rw [four_add_pt]
  set f0 := (SchwartzMap.smulLeftCLM ℂ (fun x => @inner ℝ _ _ x e₀)) ψ
  set f1 := (SchwartzMap.smulLeftCLM ℂ (fun x => @inner ℝ _ _ x e₁)) ψ
  have hfour_f0 : FourierTransform.fourier ((2 * ↑Real.pi * Complex.I) • f0) =
    -(LineDeriv.lineDerivOp e₀ φ) := by
    have hsm := FourierSMul.fourier_smul (-(2 * ↑Real.pi * Complex.I)) f0
    rw [neg_smul] at hsm h0
    rw [hsm] at h0
    have hsm2 := FourierSMul.fourier_smul (2 * ↑Real.pi * Complex.I) f0
    rw [hsm2, h0, neg_smul, neg_neg]
  have hfour_f1 : FourierTransform.fourier ((2 * ↑Real.pi * Complex.I) • f1) =
    -(LineDeriv.lineDerivOp e₁ φ) := by
    have hsm := FourierSMul.fourier_smul (-(2 * ↑Real.pi * Complex.I)) f1
    rw [neg_smul] at hsm h1
    rw [hsm] at h1
    have hsm2 := FourierSMul.fourier_smul (2 * ↑Real.pi * Complex.I) f1
    rw [hsm2, h1, neg_smul, neg_neg]
  have hfour_I_f1 : FourierTransform.fourier (Complex.I • ((2 * ↑Real.pi * Complex.I) • f1)) =
    Complex.I • (-(LineDeriv.lineDerivOp e₁ φ)) := by
    rw [FourierSMul.fourier_smul, hfour_f1]
  have hfour_sum_pt := congr_fun (congrArg DFunLike.coe
    (show FourierTransform.fourier ((2 * ↑Real.pi * Complex.I) • f0) +
      FourierTransform.fourier (Complex.I • ((2 * ↑Real.pi * Complex.I) • f1)) =
      -(LineDeriv.lineDerivOp e₀ φ) + Complex.I • (-(LineDeriv.lineDerivOp e₁ φ))
    from by rw [hfour_f0, hfour_I_f1])) ξ
  simp only [SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply] at hfour_sum_pt
  rw [hfour_sum_pt]
  simp only [smul_neg]
  rw [← neg_add]
/-- The Fourier-side integral identity for the Cauchy-Riemann kernel: integrating the Fourier
multiplier by `polySymbol 2 dbarPoly` of `𝓕⁻¹ φ` against the Cauchy-Riemann kernel recovers
`φ(0)`. -/
end DifferentialOperators


/--
[cauchyRiemannKernel_locallyIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
private lemma cauchyRiemannKernel_locallyIntegrable_eq :
-- imply
  LocallyIntegrable cauchyRiemannKernel (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
-- proof
  apply DifferentialOperators.cauchyRiemannKernel_locallyIntegrable

/--
[complex_norm_eq_euclidean_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
private lemma complex_norm_eq_euclidean_norm_eq
  {v : EuclideanSpace ℝ (Fin 2)} :
-- imply
  ‖((v 0 : ℂ) + Complex.I * (v 1 : ℂ))‖ = ‖v‖ := by
-- proof
  apply DifferentialOperators.complex_norm_eq_euclidean_norm v

/--
[cauchyRiemannKernel_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
private lemma cauchyRiemannKernel_norm_le_eq
  {v : EuclideanSpace ℝ (Fin 2)}
-- given
  (hv : 1 ≤ ‖v‖) :
-- imply
  ‖cauchyRiemannKernel v‖ ≤ (2 * Real.pi)⁻¹ := by
-- proof
  apply DifferentialOperators.cauchyRiemannKernel_norm_le v hv

/--
[cauchyRiemannKernel_schwartz_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
private lemma cauchyRiemannKernel_schwartz_integrable_eq
  {φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)} :
-- imply
  Integrable (fun v => φ v • cauchyRiemannKernel v) volume := by
-- proof
  apply DifferentialOperators.cauchyRiemannKernel_schwartz_integrable φ

/--
[cauchyRiemannKernel_integral_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean)
-/
@[path]
private lemma cauchyRiemannKernel_integral_bound_eq :
-- imply
  ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)), ‖∫ v, φ v • cauchyRiemannKernel v‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2)) ℂ)) φ := by
-- proof
  apply DifferentialOperators.cauchyRiemannKernel_integral_bound


-- created on 2026-10-23
