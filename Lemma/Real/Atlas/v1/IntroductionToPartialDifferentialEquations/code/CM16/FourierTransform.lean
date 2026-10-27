import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
open MeasureTheory Complex Finset SchwartzMap FourierAnalysis
open scoped FourierTransform RealInnerProductSpace


namespace FourierAnalysis

/--
[fourierTransform_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransform_bound
  {f : ℝ → ℂ}
  {ξ : ℝ}
-- given
  (hf : Integrable f) :
-- imply
  ‖fourierTransform f ξ‖ ≤ ∫ x : ℝ, ‖f x‖ := by
-- proof
  unfold fourierTransform
  calc ‖∫ x, f x * exp (↑(-2 * Real.pi * ξ * x) * I)‖
    ≤ ∫ x, ‖f x * exp (↑(-2 * Real.pi * ξ * x) * I)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ := by
      congr 1; ext x
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransform_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransform_continuous
  {f : ℝ → ℂ}
-- given
  (hf : Integrable f) :
-- imply
  Continuous (fourierTransform f) := by
-- proof
  unfold fourierTransform
  apply continuous_of_dominated (bound := fun x => ‖f x‖)
  ·
    intro ξ
    apply AEStronglyMeasurable.mul hf.aestronglyMeasurable
    apply (Complex.continuous_exp.comp ?_).aestronglyMeasurable
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp
      (((continuous_const.mul continuous_const).mul continuous_const).mul continuous_id)
    · exact continuous_const
  ·
    intro ξ
    exact ae_of_all _ (fun x => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one])
  ·
    exact hf.norm
  ·
    exact ae_of_all _ (fun x => by
      apply Continuous.mul continuous_const
      apply Complex.continuous_exp.comp
      apply Continuous.mul _ continuous_const
      apply Complex.continuous_ofReal.comp
      exact (continuous_const.mul continuous_id).mul continuous_const)

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransform_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransform_tendsto_zero
  {f : ℝ → ℂ}
-- given
  (_hf : Integrable f) :
-- imply
  Filter.Tendsto (fourierTransform f) (Filter.cocompact ℝ) (nhds 0) := by
-- proof
  have heq : fourierTransform f = 𝓕 f := by
    ext ξ; unfold fourierTransform
    rw [Real.fourier_eq']; congr 1; ext x
    rw [smul_eq_mul, mul_comm]; congr 1; congr 1; congr 1
    simp only [inner, Inner.inner, starRingEnd_apply, star_trivial, RCLike.re_to_real]
    push_cast; ring
  rw [heq]
  exact Real.zero_at_infty_fourier f

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_L1_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_L1_properties
  {f : ℝ → ℂ}
-- given
  (hf : Integrable f) :
-- imply
  Continuous (fourierTransform f) ∧ (∀ ξ : ℝ, ‖fourierTransform f ξ‖ ≤ ∫ x : ℝ, ‖f x‖) ∧ Filter.Tendsto (fourierTransform f) (Filter.cocompact ℝ) (nhds 0) :=
-- proof
  ⟨fourierTransform_continuous f hf,
    fourierTransform_bound f hf,
    fourierTransform_tendsto_zero f hf⟩

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_translate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_translate
  {f : ℝ → ℂ}
  {y ξ : ℝ}
-- given
  (hf : Integrable f) :
-- imply
  fourierTransform (translate y f) ξ = exp (↑(-2 * Real.pi * ξ * y) * I) * fourierTransform f ξ := by
-- proof
  unfold fourierTransform translate
  have step1 : ∫ x : ℝ, f (x - y) * exp (↑(-2 * Real.pi * ξ * x) * I) =
    ∫ z : ℝ, f z * exp (↑(-2 * Real.pi * ξ * (z + y)) * I) := by
    rw [← integral_sub_right_eq_self (fun z => f z * exp (↑(-2 * Real.pi * ξ * (z + y)) * I)) y]
    congr 1; ext x; congr 1; congr 1; congr 1; push_cast; ring
  rw [step1]
  have step2 : ∀ z : ℝ, f z * exp (↑(-2 * Real.pi * ξ * (z + y)) * I) =
    exp (↑(-2 * Real.pi * ξ * y) * I) * (f z * exp (↑(-2 * Real.pi * ξ * z) * I)) := by
    intro z
    rw [show (↑(-2 * Real.pi * ξ * (z + y)) : ℂ) * I =
      ↑(-2 * Real.pi * ξ * y) * I + ↑(-2 * Real.pi * ξ * z) * I from by push_cast; ring]
    rw [Complex.exp_add]; ring
  simp_rw [step2]
  exact @MeasureTheory.integral_const_mul ℝ _ MeasureTheory.volume ℂ _
    (exp (↑(-2 * Real.pi * ξ * y) * I))
    (fun z => f z * exp (↑(-2 * Real.pi * ξ * z) * I))

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_modulate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_modulate
  {f : ℝ → ℂ}
  {η ξ : ℝ}
-- given
  (hf : Integrable f) :
-- imply
  fourierTransform (fun x => exp (↑(2 * Real.pi * η * x) * I) * f x) ξ = fourierTransform f (ξ - η) := by
-- proof
  unfold fourierTransform
  congr 1; ext x; dsimp only
  rw [show exp (↑(2 * Real.pi * η * x) * I) * f x * exp (↑(-2 * Real.pi * ξ * x) * I) =
    f x * (exp (↑(2 * Real.pi * η * x) * I) * exp (↑(-2 * Real.pi * ξ * x) * I)) from by ring,
    ← Complex.exp_add]
  congr 1; push_cast; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_dilation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_dilation
  {f : ℝ → ℂ}
  {t : ℝ}
  {ξ : ℝ}
-- given
  (hf : Integrable f)
  (ht : t ≠ 0) :
-- imply
  fourierTransform (fun x => f (t⁻¹ * x)) ξ = ↑ := by
-- proof
  unfold fourierTransform
  simp only []
  let g : ℝ → ℂ := fun y => f y * cexp (↑(-2 * Real.pi * (t * ξ) * y) * I)
  have step1 : ∫ x : ℝ, f (t⁻¹ * x) * cexp (↑(-2 * Real.pi * ξ * x) * I) =
    ∫ x : ℝ, g (t⁻¹ * x) := by
    congr 1; ext x; show _ = g (t⁻¹ * x); simp only [g]
    congr 1; congr 1; congr 1; push_cast
    have : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    field_simp
  rw [step1]
  have step2 := Measure.integral_comp_mul_left g t⁻¹
  rw [step2, inv_inv]
  show |t| • ∫ y, g y = ↑|t| * ∫ x, f x * cexp (↑(-2 * Real.pi * (t * ξ) * x) * I)
  rw [Complex.real_smul]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_convolution
  {f g : ℝ → ℂ}
  {ξ : ℝ}
-- given
  (hf : Integrable f)
  (hg : Integrable g) :
-- imply
  fourierTransform (complexConvolution f g) ξ = fourierTransform f ξ * fourierTransform g ξ := by
-- proof
  unfold fourierTransform complexConvolution
  have step1 : ∫ x : ℝ, (∫ y : ℝ, f (x - y) * g y) * cexp (↑(-2 * Real.pi * ξ * x) * I) =
    ∫ x : ℝ, ∫ y : ℝ, f (x - y) * g y * cexp (↑(-2 * Real.pi * ξ * x) * I) := by
    congr 1; ext x; exact (integral_mul_const _ _).symm
  rw [step1]
  rw [integral_integral_swap (by
    show Integrable (fun p : ℝ × ℝ => f (p.1 - p.2) * g p.2 *
      cexp (↑(-2 * Real.pi * ξ * p.1) * I)) (volume.prod volume)
    have h2 : Integrable (fun p : ℝ × ℝ => f (p.1 - p.2) * g p.2) (volume.prod volume) := by
      convert hg.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf using 1
      ext ⟨x, y⟩; simp [mul_comm]
    have hexp_cont : Continuous (fun p : ℝ × ℝ => cexp (↑(-2 * Real.pi * ξ * p.1) * I)) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_fst)).mul continuous_const)
    convert h2.bdd_mul hexp_cont.aestronglyMeasurable
      (ae_of_all _ (fun p => by rw [Complex.norm_exp_ofReal_mul_I])) using 1
    ext ⟨x, y⟩; ring)]
  simp_rw [show ∀ y : ℝ, (∫ x : ℝ, f (x - y) * g y * cexp (↑(-2 * Real.pi * ξ * x) * I)) =
    ∫ u : ℝ, f u * g y * cexp (↑(-2 * Real.pi * ξ * (u + y)) * I) from fun y => by
    rw [← integral_sub_right_eq_self
      (fun u => f u * g y * cexp (↑(-2 * Real.pi * ξ * (u + y)) * I)) y]
    congr 1; ext x; congr 1; congr 1; congr 1; ring]
  simp_rw [show ∀ u y : ℝ,
    cexp (↑(-2 * Real.pi * ξ * (u + y)) * I) =
    cexp (↑(-2 * Real.pi * ξ * u) * I) * cexp (↑(-2 * Real.pi * ξ * y) * I) from fun u y => by
    rw [show (↑(-2 * Real.pi * ξ * (u + y)) : ℂ) * I =
      (↑(-2 * Real.pi * ξ * u) : ℂ) * I + (↑(-2 * Real.pi * ξ * y) : ℂ) * I from by
      push_cast; ring]
    exact Complex.exp_add _ _]
  simp_rw [show ∀ y u : ℝ,
    f u * g y * (cexp (↑(-2 * Real.pi * ξ * u) * I) * cexp (↑(-2 * Real.pi * ξ * y) * I)) =
    (g y * cexp (↑(-2 * Real.pi * ξ * y) * I)) * (f u * cexp (↑(-2 * Real.pi * ξ * u) * I))
    from fun y u => by ring]
  simp_rw [show ∀ y : ℝ,
    (∫ u : ℝ, g y * cexp (↑(-2 * Real.pi * ξ * y) * I) *
      (f u * cexp (↑(-2 * Real.pi * ξ * u) * I))) =
    g y * cexp (↑(-2 * Real.pi * ξ * y) * I) *
      ∫ u : ℝ, f u * cexp (↑(-2 * Real.pi * ξ * u) * I)
    from fun y => integral_const_mul _ _]
  trans (∫ y : ℝ, g y * cexp (↑(-2 * Real.pi * ξ * y) * I)) *
    (∫ u : ℝ, f u * cexp (↑(-2 * Real.pi * ξ * u) * I))
  · exact integral_mul_const _ _
  · ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_deriv_freq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_deriv_freq
  {f : ℝ → ℂ}
  {ξ : ℝ}
-- given
  (hf : Integrable f)
  (hxf : Integrable (fun x => (x : ℝ) * f x)) :
-- imply
  deriv (fourierTransform f) ξ = fourierTransform (fun x => ↑(-2 * Real.pi) * I * ↑x * f x) ξ := by
-- proof
  have hbridge : ∀ (g : ℝ → ℂ) (y : ℝ), fourierTransform g y = 𝓕 g y := by
    intro g y; unfold fourierTransform
    rw [Real.fourier_eq']
    congr 1; ext v
    rw [smul_eq_mul, mul_comm]; congr 1; congr 1; congr 1; congr 1
    simp only [inner, Inner.inner, starRingEnd_apply, star_trivial, RCLike.re_to_real, mul_comm]
    ring
  have heq : fourierTransform f = 𝓕 f := funext (hbridge f)
  have hxf' : Integrable (fun x : ℝ => x • f x) := by
    simp only [Complex.real_smul]; exact hxf
  have hmathlib := _root_.Real.deriv_fourier hf hxf'
  have lhs_eq : deriv (fourierTransform f) = deriv (𝓕 f) := by rw [heq]
  rw [lhs_eq, congr_fun hmathlib ξ, ← hbridge]
  congr 1; ext x; simp [smul_eq_mul]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_of_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_of_deriv
  {f : ℝ → ℂ}
  {ξ : ℝ}
-- given
  (hf_int : Integrable f)
  (hf'_int : Integrable (deriv f))
  (hf_decay : Filter.Tendsto f (Filter.cocompact ℝ) (nhds 0))
  (hf_diff : Differentiable ℝ f := by fun_prop) :
-- imply
  fourierTransform (deriv f) ξ = ↑(2 * Real.pi) * I * ↑ξ * fourierTransform f ξ := by
-- proof
  have hbridge : ∀ (g : ℝ → ℂ) (y : ℝ), fourierTransform g y = 𝓕 g y := by
    intro g y; unfold fourierTransform
    rw [Real.fourier_eq']
    congr 1; ext v
    rw [smul_eq_mul, mul_comm]; congr 1; congr 1; congr 1; congr 1
    simp only [inner, Inner.inner, starRingEnd_apply, star_trivial, RCLike.re_to_real, mul_comm]
    ring
  rw [hbridge, hbridge]
  have hmathlib := _root_.Real.fourier_deriv hf_int hf_diff hf'_int
  have h1 : 𝓕 (deriv f) ξ = (2 * ↑Real.pi * I * ↑ξ) • 𝓕 f ξ := congr_fun hmathlib ξ
  rw [h1, smul_eq_mul]
  push_cast
  ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_conj
  {f : ℝ → ℂ}
  {ξ : ℝ}
-- given
  (hf : Integrable f) :
-- imply
  starRingEnd ℂ (fourierTransform f ξ) = inverseFourierTransform (fun x => starRingEnd ℂ (f x)) ξ := by
-- proof
  unfold fourierTransform inverseFourierTransform
  simp only []
  have h1 : (starRingEnd ℂ) (∫ (x : ℝ), f x * cexp (↑(-2 * Real.pi * ξ * x) * I)) =
    ∫ x : ℝ, (starRingEnd ℂ) (f x * cexp (↑(-2 * Real.pi * ξ * x) * I)) := by
    exact (integral_conj (𝕜 := ℂ)
      (f := fun x => f x * cexp (↑(-2 * Real.pi * ξ * x) * I))).symm
  rw [h1]
  congr 1; ext x
  rw [map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_reverse_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_reverse_conj
  {f : ℝ → ℂ}
  {ξ : ℝ}
-- given
  (hf : Integrable f) :
-- imply
  starRingEnd ℂ (inverseFourierTransform f ξ) = fourierTransform (fun x => starRingEnd ℂ (f x)) ξ := by
-- proof
  unfold inverseFourierTransform fourierTransform
  simp only []
  have h1 : (starRingEnd ℂ) (∫ (x : ℝ), f x * cexp (↑(2 * Real.pi * x * ξ) * I)) =
    ∫ x : ℝ, (starRingEnd ℂ) (f x * cexp (↑(2 * Real.pi * x * ξ) * I)) :=
    (integral_conj (𝕜 := ℂ) (f := fun x => f x * cexp (↑(2 * Real.pi * x * ξ) * I))).symm
  rw [h1]
  congr 1; ext x
  rw [map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_translateND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_translateND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {y ξ : Fin n → ℝ}
-- given
  (hf : Integrable f) :
-- imply
  fourierTransformND n (translateFn y f) ξ = cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * y j)) * fourierTransformND n f ξ := by
-- proof
  unfold fourierTransformND translateFn
  have step1 : ∫ x : Fin n → ℝ, f (x - y) * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j)) =
    ∫ z : Fin n → ℝ, f z * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * (z j + y j))) := by
    rw [← integral_sub_right_eq_self
      (fun z => f z * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * (z j + y j)))) y]
    congr 1; ext x
    congr 1; congr 1; congr 1
    simp only [Pi.sub_apply, sub_add_cancel]
  rw [step1]
  have step2 : ∀ z : Fin n → ℝ,
    f z * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * (z j + y j))) =
    cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * y j)) *
      (f z * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * z j))) := by
    intro z
    rw [show (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * (z j + y j)) : ℂ) =
      ↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * y j) +
      ↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * z j) from by
      push_cast; simp only [mul_add, Finset.sum_add_distrib]; ring]
    rw [Complex.exp_add]; ring
  simp_rw [step2]
  exact integral_const_mul _ _

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_modulateND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_modulateND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {η ξ : Fin n → ℝ}
-- given
  (hf : Integrable f) :
-- imply
  fourierTransformND n (fun x => cexp (↑(2 * Real.pi) * I * ↑(∑ j, η j * x j)) * f x) ξ = fourierTransformND n f (ξ - η) := by
-- proof
  unfold fourierTransformND
  congr 1; ext x; dsimp only
  rw [show cexp (↑(2 * Real.pi) * I * ↑(∑ j : Fin n, η j * x j)) * f x *
    cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * x j)) =
    f x * (cexp (↑(2 * Real.pi) * I * ↑(∑ j : Fin n, η j * x j)) *
      cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * x j))) from by ring,
    ← Complex.exp_add]
  congr 1
  have hsum : (∑ j : Fin n, (ξ j - η j) * x j) =
    (∑ j : Fin n, ξ j * x j) - (∑ j : Fin n, η j * x j) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; ring
  simp only [Pi.sub_apply]
  rw [hsum]
  push_cast; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_convolutionND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_convolutionND
  {n : ℕ}
  {f g : (Fin n → ℝ) → ℂ}
  {ξ : Fin n → ℝ}
-- given
  (hf : Integrable f)
  (hg : Integrable g)
  (hfg : Integrable (Function.uncurry (fun x y => f y * g (x - y) * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j)))) (volume.prod volume)) :
-- imply
  fourierTransformND n (complexConvolutionND f g) ξ = fourierTransformND n f ξ * fourierTransformND n g ξ := by
-- proof
  unfold fourierTransformND complexConvolutionND
  have step1 : ∫ x : Fin n → ℝ, (∫ y : Fin n → ℝ, f y * g (x - y)) *
    cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j)) =
    ∫ x : Fin n → ℝ, ∫ y : Fin n → ℝ, f y * g (x - y) *
      cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j)) := by
    congr 1; ext x; exact (integral_mul_const _ _).symm
  rw [step1]
  rw [integral_integral_swap hfg]
  simp_rw [show ∀ y : Fin n → ℝ,
    (∫ x : Fin n → ℝ, f y * g (x - y) * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j))) =
    ∫ u : Fin n → ℝ, f y * g u * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * (u j + y j)))
    from fun y => by
    rw [← integral_sub_right_eq_self
      (fun u => f y * g u * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * (u j + y j)))) y]
    congr 1; ext x
    simp only [Pi.sub_apply, sub_add_cancel]]
  have hsplit : ∀ u y : Fin n → ℝ,
    f y * g u * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * (u j + y j))) =
    (f y * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * y j))) *
      (g u * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * u j))) := by
    intro u y
    rw [show (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * (u j + y j)) : ℂ) =
      ↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * u j) +
      ↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * y j) from by
      push_cast; simp_rw [mul_add, Finset.sum_add_distrib]; ring]
    rw [Complex.exp_add]; ring
  simp_rw [hsplit]
  simp_rw [show ∀ y : Fin n → ℝ,
    (∫ u : Fin n → ℝ, f y * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * y j)) *
      (g u * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * u j)))) =
    f y * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * y j)) *
      ∫ u : Fin n → ℝ, g u * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * u j))
    from fun y => integral_const_mul _ _]
  trans (∫ y : Fin n → ℝ, f y * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * y j))) *
    (∫ u : Fin n → ℝ, g u * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, ξ j * u j)))
  · exact integral_mul_const _ _
  · ring

end FourierAnalysis

namespace FourierAnalysis

/--
[sum_update_decomp_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma sum_update_decomp_coord
  {n : ℕ}
  {ξ : Fin n → ℝ}
  {i : Fin n}
  {t : ℝ}
  {x : Fin n → ℝ} :
-- imply
  ∑ j : Fin n, (Function.update ξ i t) j * x j = t * x i + ∑ j ∈ Finset.univ.erase i, ξ j * x j := by
-- proof
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp [Function.update_self]
  · exact Finset.sum_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

end FourierAnalysis

namespace FourierAnalysis

/--
[continuous_cexp_update_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma continuous_cexp_update_coord
  {n : ℕ}
  {ξ : Fin n → ℝ}
  {i : Fin n}
  {t : ℝ} :
-- imply
  Continuous (fun x : Fin n → ℝ => cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, (Function.update ξ i t) j * x j))) :=
-- proof
  (continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j))))).cexp
set_option maxHeartbeats 3200000 in

end FourierAnalysis

namespace FourierAnalysis

/--
[hasDerivAt_fourierTransformND_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma hasDerivAt_fourierTransformND_coord
  {n : ℕ}
  {g : (Fin n → ℝ) → ℂ}
  {i : Fin n}
  {ξ : Fin n → ℝ}
-- given
  (hg_int : Integrable g)
  (hxg_int : Integrable (fun x => ↑(x i) * g x)) :
-- imply
  HasDerivAt (fun t => fourierTransformND n g (Function.update ξ i t)) (fourierTransformND n (fun x => ↑(-2 * Real.pi) * I * ↑(x i) * g x) ξ) (ξ i) := by
-- proof
  unfold fourierTransformND
  set F : ℝ → (Fin n → ℝ) → ℂ := fun t x =>
    g x * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, (Function.update ξ i t) j * x j))
  set F' : ℝ → (Fin n → ℝ) → ℂ := fun t x =>
    ↑(-2 * Real.pi) * I * ↑(x i) * g x *
      cexp (↑(-2 * Real.pi) * I * ↑(∑ j, (Function.update ξ i t) j * x j))
  set bound : (Fin n → ℝ) → ℝ := fun x => 2 * Real.pi * |x i| * ‖g x‖
  suffices h : HasDerivAt (fun t => ∫ x, F t x) (∫ x, F' (ξ i) x) (ξ i) by
    convert h using 2
    ext x; simp only [F']
    congr 1; congr 1; congr 1
    simp [Function.update_eq_self]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (s := Set.univ)
    (Filter.univ_mem' (fun _ => trivial))
    (Filter.Eventually.of_forall fun t =>
      hg_int.aestronglyMeasurable.mul (continuous_cexp_update_coord ξ i t).aestronglyMeasurable)
    (hg_int.mono (hg_int.aestronglyMeasurable.mul
      (continuous_cexp_update_coord ξ i (ξ i)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        simp only [F, norm_mul]
        rw [show ↑(-2 * Real.pi) * I * ↑(∑ j, Function.update ξ i (ξ i) j * x j) =
          ↑((-2 * Real.pi) * ∑ j, Function.update ξ i (ξ i) j * x j) * I from by push_cast; ring]
        rw [Complex.norm_exp_ofReal_mul_I, mul_one]))
    (((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i))).aestronglyMeasurable.mul
      hg_int.aestronglyMeasurable).mul (continuous_cexp_update_coord ξ i (ξ i)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x t _ => by
      simp only [F', bound]
      rw [show (↑(-2 * Real.pi) : ℂ) * I * ↑(x i) * g x *
        cexp (↑(-2 * Real.pi) * I * ↑(∑ j, (Function.update ξ i t) j * x j)) =
        ((↑(-2 * Real.pi) * I) * (↑(x i) * g x)) *
          cexp (↑((-2 * Real.pi) * ∑ j, (Function.update ξ i t) j * x j) * I)
        from by push_cast; ring]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul]
      rw [show ‖(↑(-2 * Real.pi) : ℂ) * I‖ = 2 * Real.pi from by
        simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_neg]
        simp [abs_of_pos Real.pi_pos]]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact le_of_eq (by ring))
    (by
      have h1 : Integrable (fun x : Fin n → ℝ => |x i| * ‖g x‖) := by
        have := hxg_int.norm
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
        exact this
      convert h1.const_mul (2 * Real.pi) using 1; ext x; ring)
    (Filter.Eventually.of_forall fun x t _ => by
      simp only [F, F']
      simp_rw [sum_update_decomp_coord ξ i _ x]
      set C := ∑ j ∈ Finset.univ.erase i, ξ j * x j
      have hlin : ∀ t', (↑(-2 * Real.pi) : ℂ) * I * ↑(t' * x i + C) =
        ↑(-2 * Real.pi) * I * ↑(x i) * ↑t' + ↑(-2 * Real.pi) * I * ↑C := by
        intro t'; push_cast; ring
      simp_rw [hlin]
      set a := (↑(-2 * Real.pi) : ℂ) * I * ↑(x i)
      set b := (↑(-2 * Real.pi) : ℂ) * I * ↑C
      have hcexp : HasDerivAt (fun t' : ℝ => cexp (a * ↑t' + b)) (cexp (a * ↑t + b) * a) t := by
        have h1 : HasDerivAt (fun t' : ℝ => (a * ↑t' + b : ℂ)) a t := by
          have hd := (hasDerivAt_id t).ofReal_comp.const_mul a
          simp only [ofReal_one, mul_one] at hd
          exact hd.add_const b
        exact h1.cexp
      have hfull := hcexp.const_smul (g x)
      simp only [smul_eq_mul] at hfull
      convert hfull using 1; ring)).2

end FourierAnalysis

namespace FourierAnalysis

/--
[integrable_pow_xi_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma integrable_pow_xi_mul
  {n : ℕ}
  {i : Fin n}
  {g : (Fin n → ℝ) → ℂ}
  {k : ℕ}
-- given
  (hg_int : Integrable g)
  (hkg : Integrable (fun x => ↑(|x i| ^ k) * g x)) :
-- imply
  Integrable (fun x => (↑(-2 * Real.pi) * I * ↑(x i)) ^ k * g x) := by
-- proof
  rw [show (fun x => (↑(-2 * Real.pi) * I * ↑(x i)) ^ k * g x) =
    (fun x => (↑(-2 * Real.pi) * I) ^ k * (↑(x i) ^ k * g x)) from by ext x; ring]
  apply Integrable.const_mul
  exact hkg.mono
    (((Complex.continuous_ofReal.comp (continuous_apply i)).pow k).aestronglyMeasurable.mul
      hg_int.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_abs]
      exact le_refl _)
set_option maxHeartbeats 3200000 in

end FourierAnalysis

namespace FourierAnalysis

/--
[iteratedPartialDeriv_fourierTransformND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma iteratedPartialDeriv_fourierTransformND
  {n : ℕ}
  {i : Fin n}
  {k : ℕ}
  {g : (Fin n → ℝ) → ℂ}
  {ξ : Fin n → ℝ}
-- given
  (hg_int : Integrable g)
  (hkg_int : ∀ j ≤ k, Integrable (fun x => ↑(|x i| ^ j) * g x)) :
-- imply
  iteratedPartialDeriv i k (fourierTransformND n g) ξ = fourierTransformND n (fun x => (↑(-2 * Real.pi) * I * ↑(x i)) ^ k * g x) ξ := by
-- proof
  induction k generalizing ξ with
  | zero =>
    simp only [iteratedPartialDeriv, Function.iterate_zero, id, pow_zero, one_mul]
  | succ k ih =>
    have hsucc : iteratedPartialDeriv i (k + 1) (fourierTransformND n g) =
      (fun x => deriv (fun t => iteratedPartialDeriv i k (fourierTransformND n g)
        (Function.update x i t)) (x i)) := by
      unfold iteratedPartialDeriv; rw [Function.iterate_succ']; rfl
    rw [hsucc]
    set g_k := fun x => (↑(-2 * Real.pi) * I * ↑(x i)) ^ k * g x with hg_k_def
    have hIH : ∀ ξ', iteratedPartialDeriv i k (fourierTransformND n g) ξ' =
      fourierTransformND n g_k ξ' :=
      fun ξ' => ih (fun j hj => hkg_int j (Nat.le_succ_of_le hj)) ξ'
    simp_rw [hIH]
    have hgk_int : Integrable g_k :=
      integrable_pow_xi_mul hg_int (hkg_int k (Nat.le_succ k))
    have hxgk_int : Integrable (fun x => ↑(x i) * g_k x) := by
      rw [show (fun x => (↑(x i) : ℂ) * g_k x) =
        fun x => (↑(-2 * Real.pi) * I) ^ k * (↑(x i) ^ (k + 1) * g x) from by
        ext x; simp only [hg_k_def]; ring]
      apply Integrable.const_mul
      exact (hkg_int (k + 1) le_rfl).mono
        (((Complex.continuous_ofReal.comp (continuous_apply i)).pow (k + 1)).aestronglyMeasurable.mul
          hg_int.aestronglyMeasurable)
        (ae_of_all _ fun x => by
          simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_abs]
          exact le_refl _)
    rw [(hasDerivAt_fourierTransformND_coord g_k i ξ hgk_int hxgk_int).deriv]
    congr 1; ext x; simp only [hg_k_def]; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransformND_partialDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransformND_partialDeriv
  {n : ℕ}
  {g : (Fin n → ℝ) → ℂ}
  {j : Fin n}
  {ξ : Fin n → ℝ}
-- given
  (hg_diff : Differentiable ℝ g)
  (hg_int : Integrable g)
  (hg'_int : Integrable (fun x => deriv (fun t => g (Function.update x j t)) (x j)))
  (hg_decay : Filter.Tendsto g (Filter.cocompact _) (nhds 0)) :
-- imply
  fourierTransformND n (fun x => deriv (fun t => g (Function.update x j t)) (x j)) ξ = ↑(2 * Real.pi) * I * ↑(ξ j) * fourierTransformND n g ξ := by
-- proof
  have hpartial : ∀ x, deriv (fun t => g (Function.update x j t)) (x j) =
    fderiv ℝ g x (Pi.single j 1) := by
    intro x
    have h1 : HasDerivAt (Function.update x j) (Pi.single j 1) (x j) :=
      _root_.hasDerivAt_update x j (x j)
    have heq : Function.update x j (x j) = x := Function.update_eq_self j x
    have h2 : HasFDerivAt g (fderiv ℝ g x) x := (hg_diff x).hasFDerivAt
    have h2' : HasFDerivAt g (fderiv ℝ g x) (Function.update x j (x j)) := by rw [heq]; exact h2
    have h3 : HasDerivAt (g ∘ Function.update x j) ((fderiv ℝ g x) (Pi.single j 1)) (x j) :=
      h2'.comp_hasDerivAt (x j) h1
    exact h3.deriv
  let L : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ k : Fin n, (ξ k) • (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)
  have hL_apply : ∀ y, L y = ∑ k : Fin n, ξ k * y k := by
    intro y
    simp [L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
  let cL : (Fin n → ℝ) →L[ℝ] ℂ :=
    (↑(-2 * Real.pi) * I) • (Complex.ofRealCLM.comp L)
  have hcL_apply : ∀ y, cL y = ↑(-2 * Real.pi) * I * ↑(L y) := by
    intro y
    simp [cL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
  set e : (Fin n → ℝ) → ℂ := fun x => cexp (cL x) with he_def
  have he_eq : ∀ x, e x = cexp (↑(-2 * Real.pi) * I * ↑(∑ k : Fin n, ξ k * x k)) := by
    intro x; simp only [he_def, hcL_apply, hL_apply]
  have he_hasFDerivAt : ∀ x, HasFDerivAt e (e x • cL) x := by
    intro x
    exact cL.hasFDerivAt.cexp
  have he_diff : Differentiable ℝ e := fun x => (he_hasFDerivAt x).differentiableAt
  have hfderiv_e : ∀ x, fderiv ℝ e x (Pi.single j 1) =
    ↑(-2 * Real.pi) * I * ↑(ξ j) * e x := by
    intro x
    rw [(he_hasFDerivAt x).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hcL_apply]
    have hLsingle : L (Pi.single j 1) = ξ j := by
      rw [hL_apply]
      simp [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    rw [hLsingle]
    ring
  have he_norm : ∀ x, ‖e x‖ = 1 := by
    intro x
    rw [he_def, Complex.norm_exp, hcL_apply]
    have : (↑(-2 * Real.pi) * I * ↑(L x) : ℂ).re = 0 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [this, Real.exp_zero]
  have he_cont : Continuous e := he_diff.continuous
  unfold fourierTransformND
  simp_rw [hpartial, show ∀ x, cexp (↑(-2 * Real.pi) * I * ↑(∑ j_1 : Fin n, ξ j_1 * x j_1)) = e x
    from fun x => (he_eq x).symm]
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := e) (g := g) (v := Pi.single j 1) (μ := volume)
    (by
      have hint : Integrable (fun x => e x * g x) :=
        hg_int.bdd_mul he_cont.aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => le_of_eq (he_norm x))
      exact (hint.const_mul (↑(-2 * Real.pi) * I * ↑(ξ j))).congr
        (Filter.Eventually.of_forall fun x => by
          show ↑(-2 * Real.pi) * I * ↑(ξ j) * (e x * g x) = fderiv ℝ e x (Pi.single j 1) * g x
          rw [hfderiv_e]; ring))
    (by
      have h : Integrable (fun x => fderiv ℝ g x (Pi.single j 1)) := by
        exact hg'_int.congr (Filter.Eventually.of_forall fun x => hpartial x)
      exact h.bdd_mul he_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => le_of_eq (he_norm x)))
    (by
      exact hg_int.bdd_mul he_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => le_of_eq (he_norm x)))
    (fun x _ => he_diff x)
    (fun x _ => hg_diff x)
  calc ∫ x, fderiv ℝ g x (Pi.single j 1) * e x
    = ∫ x, e x * fderiv ℝ g x (Pi.single j 1) := by congr 1; ext x; ring
    _ = -(∫ x, fderiv ℝ e x (Pi.single j 1) * g x) := ibp
    _ = -(∫ x, ↑(-2 * Real.pi) * I * ↑(ξ j) * e x * g x) := by
      congr 1; congr 1; ext x; rw [hfderiv_e]
    _ = -(↑(-2 * Real.pi) * I * ↑(ξ j)) * (∫ x, e x * g x) := by
      rw [show -(↑(-2 * Real.pi) * I * ↑(ξ j)) * (∫ x, e x * g x) =
        -(↑(-2 * Real.pi) * I * ↑(ξ j) * ∫ x, e x * g x) from by ring]
      congr 1
      rw [show (fun x => ↑(-2 * Real.pi) * I * ↑(ξ j) * e x * g x) =
        (fun x => (↑(-2 * Real.pi) * I * ↑(ξ j)) * (e x * g x)) from by ext x; ring]
      exact integral_const_mul (↑(-2 * Real.pi) * I * ↑(ξ j) : ℂ) (fun x => e x * g x)
    _ = -(↑(-2 * Real.pi) * I * ↑(ξ j)) * (∫ x, g x * e x) := by
      congr 1; congr 1; ext x; ring
    _ = ↑(2 * Real.pi) * I * ↑(ξ j) * (∫ x, g x * e x) := by push_cast; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[iteratedPartialDeriv_succ_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma iteratedPartialDeriv_succ_apply
  {n : ℕ}
  {j : Fin n}
  {k : ℕ}
  {g : (Fin n → ℝ) → ℂ} :
-- imply
  iteratedPartialDeriv j (k + 1) g = (fun x => deriv (fun t => iteratedPartialDeriv j k g (Function.update x j t)) (x j)) := by
-- proof
  unfold iteratedPartialDeriv
  rw [Function.iterate_succ']
  rfl

end FourierAnalysis

namespace FourierAnalysis

/--
[partialDeriv_eq_fderiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma partialDeriv_eq_fderiv_apply
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {j : Fin n}
-- given
  (hf : Differentiable ℝ f) :
-- imply
  (fun x => deriv (fun t => f (Function.update x j t)) (x j)) = (fun x => fderiv ℝ f x (Pi.single j 1)) := by
-- proof
  ext x
  have h1 : HasDerivAt (Function.update x j) (Pi.single j 1) (x j) :=
    _root_.hasDerivAt_update x j (x j)
  have heq : Function.update x j (x j) = x := Function.update_eq_self j x
  have h2 : HasFDerivAt f (fderiv ℝ f x) x := (hf x).hasFDerivAt
  have h2' : HasFDerivAt f (fderiv ℝ f x) (Function.update x j (x j)) := by rw [heq]; exact h2
  have h3 : HasDerivAt (f ∘ Function.update x j) ((fderiv ℝ f x) (Pi.single j 1)) (x j) :=
    h2'.comp_hasDerivAt (x j) h1
  exact h3.deriv

end FourierAnalysis

namespace FourierAnalysis

/--
[contDiff_partialDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma contDiff_partialDeriv
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {j : Fin n}
  {m : ℕ}
-- given
  (hf : ContDiff ℝ (↑(m + 1)) f) :
-- imply
  ContDiff ℝ (↑m) (fun x => deriv (fun t => f (Function.update x j t)) (x j)) := by
-- proof
  have hdiff : Differentiable ℝ f := by
    apply hf.differentiable
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [partialDeriv_eq_fderiv_apply f j hdiff]
  exact (_root_.contDiff_succ_iff_fderiv_apply (n := ↑m) (f := f) |>.mp (by exact_mod_cast hf)).2.2
    (Pi.single j 1)

end FourierAnalysis

namespace FourierAnalysis

/--
[contDiff_iteratedPartialDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma contDiff_iteratedPartialDeriv
  {n : ℕ}
  {j : Fin n}
  {k : ℕ}
  {g : (Fin n → ℝ) → ℂ}
  {m : ℕ}
-- given
  (hg : ContDiff ℝ (↑(k + m)) g) :
-- imply
  ContDiff ℝ (↑m) (iteratedPartialDeriv j k g) := by
-- proof
  induction k generalizing g m with
  | zero =>
    simp only [iteratedPartialDeriv, Function.iterate_zero, id_eq, Nat.zero_add] at hg ⊢
    exact hg
  | succ k ih =>
    simp only [iteratedPartialDeriv, Function.iterate_succ']
    change ContDiff ℝ ↑m
      (fun x => deriv (fun t => iteratedPartialDeriv j k g (Function.update x j t)) (x j))
    have hk_smooth : ContDiff ℝ (↑(m + 1)) (iteratedPartialDeriv j k g) := by
      apply ih
      have h : k + (m + 1) = k + 1 + m := by omega
      rw [h]; exact hg
    exact contDiff_partialDeriv _ j m hk_smooth

end FourierAnalysis

namespace FourierAnalysis

/--
[iteratedPartialDeriv_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma iteratedPartialDeriv_differentiable
  {n : ℕ}
  {j : Fin n}
  {k : ℕ}
  {g : (Fin n → ℝ) → ℂ}
-- given
  (hg : ContDiff ℝ (↑(k + 1)) g) :
-- imply
  Differentiable ℝ (iteratedPartialDeriv j k g) := by
-- proof
  have h := contDiff_iteratedPartialDeriv j k g 1 hg
  exact h.differentiable (by simp only [ne_eq, Nat.cast_eq_zero]; omega)

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransformND_iteratedPartialDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransformND_iteratedPartialDeriv
  {n : ℕ}
  {g : (Fin n → ℝ) → ℂ}
  {j : Fin n}
  {k : ℕ}
  {ξ : Fin n → ℝ}
-- given
  (hg_smooth : ContDiff ℝ (↑k) g)
  (hg_deriv_int : ∀ m : ℕ, m ≤ k → Integrable (iteratedPartialDeriv j m g))
  (hg_deriv_decay : ∀ m : ℕ, m ≤ k - 1 → Filter.Tendsto (iteratedPartialDeriv j m g) (Filter.cocompact _) (nhds 0)) :
-- imply
  fourierTransformND n (iteratedPartialDeriv j k g) ξ = (↑(2 * Real.pi) * I * ↑(ξ j)) ^ k * fourierTransformND n g ξ := by
-- proof
  induction k with
  | zero =>
    simp [iteratedPartialDeriv, pow_zero, one_mul]
  | succ k ih =>
    rw [iteratedPartialDeriv_succ_apply]
    have hfk_diff : Differentiable ℝ (iteratedPartialDeriv j k g) :=
      iteratedPartialDeriv_differentiable j k g hg_smooth
    have hfk_int : Integrable (iteratedPartialDeriv j k g) :=
      hg_deriv_int k (Nat.le_succ k)
    have hfk_deriv_int : Integrable
      (fun x => deriv (fun t => iteratedPartialDeriv j k g (Function.update x j t)) (x j)) := by
      have h := hg_deriv_int (k + 1) le_rfl
      rwa [iteratedPartialDeriv_succ_apply] at h
    have hfk_decay : Filter.Tendsto (iteratedPartialDeriv j k g) (Filter.cocompact _) (nhds 0) :=
      hg_deriv_decay k (by omega)
    have hstep := fourierTransformND_partialDeriv (iteratedPartialDeriv j k g) j ξ
      hfk_diff hfk_int hfk_deriv_int hfk_decay
    rw [hstep]
    have hih := ih (hg_smooth.of_le (by norm_cast; omega))
      (fun m hm => hg_deriv_int m (le_trans hm (Nat.le_succ k)))
      (fun m hm => hg_deriv_decay m (by omega))
    rw [hih]
    ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_dilationND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_dilationND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {t : ℝ}
  {ξ : Fin n → ℝ}
-- given
  (hf : Integrable f)
  (ht : t ≠ 0) :
-- imply
  fourierTransformND n (fun x => f (t⁻¹ • x)) ξ = ↑(|t| ^ n) * fourierTransformND n f (t • ξ) := by
-- proof
  unfold fourierTransformND
  let g : (Fin n → ℝ) → ℂ := fun y =>
    f y * cexp (↑(-2 * Real.pi) * I * ↑(∑ j : Fin n, (t • ξ) j * y j))
  have step1 : ∫ x : Fin n → ℝ, f (t⁻¹ • x) *
    cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j)) =
    ∫ x : Fin n → ℝ, g (t⁻¹ • x) := by
    congr 1; ext x
    show f (t⁻¹ • x) * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j)) = g (t⁻¹ • x)
    simp only [g, Pi.smul_apply, smul_eq_mul]
    congr 1; congr 1; congr 1
    rw [show (∑ j : Fin n, t * ξ j * (t⁻¹ * x j)) = (∑ j : Fin n, ξ j * x j) from by
      congr 1; ext j; field_simp]
  rw [step1]
  have step2 := Measure.integral_comp_inv_smul (volume : Measure (Fin n → ℝ)) g t
  rw [step2, Module.finrank_fin_fun]
  simp only [g, Pi.smul_apply, smul_eq_mul, abs_pow]
  change ↑(|t| ^ n) * ∫ y, f y * cexp (↑(-2 * Real.pi) * I * ↑(∑ x, t * ξ x * y x)) =
    ↑(|t| ^ n) * ∫ x, f x * cexp (↑(-2 * Real.pi) * I * ↑(∑ x_1, t * ξ x_1 * x x_1))
  rfl

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_reverse_conjND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_reverse_conjND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {ξ : Fin n → ℝ}
-- given
  (hf : Integrable f) :
-- imply
  starRingEnd ℂ (inverseFourierTransformND n f ξ) = fourierTransformND n (fun x => starRingEnd ℂ (f x)) ξ := by
-- proof
  unfold inverseFourierTransformND fourierTransformND
  rw [show (∫ x : Fin n → ℝ, f x * cexp (↑(2 * Real.pi) * I * ↑(∑ j, x j * ξ j))) =
    (∫ x : Fin n → ℝ, f x * cexp (↑(2 * Real.pi) * I * ↑(∑ j, ξ j * x j))) from by
    congr 1; ext x; congr 3; congr 1
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  have h1 : (starRingEnd ℂ) (∫ x, f x * cexp (↑(2 * Real.pi) * I * ↑(∑ j, ξ j * x j))) =
    ∫ x, (starRingEnd ℂ) (f x * cexp (↑(2 * Real.pi) * I * ↑(∑ j, ξ j * x j))) :=
    (integral_conj (𝕜 := ℂ)
      (f := fun x => f x * cexp (↑(2 * Real.pi) * I * ↑(∑ j, ξ j * x j)))).symm
  rw [h1]
  congr 1; ext x
  rw [map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransform_eq_mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransform_eq_mathlib
  {f : ℝ → ℂ} :
-- imply
  fourierTransform f = 𝓕 f := by
-- proof
  ext ξ; unfold fourierTransform
  rw [Real.fourier_eq']; congr 1; ext x
  rw [smul_eq_mul, mul_comm]; congr 1; congr 1; congr 1
  simp only [inner, Inner.inner, starRingEnd_apply, star_trivial, RCLike.re_to_real]
  push_cast; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[mulByPoly_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma mulByPoly_zero
  {f : ℝ → ℂ} :
-- imply
  mulByPoly f 0 = f := by
-- proof
ext x; simp [mulByPoly]

end FourierAnalysis

namespace FourierAnalysis

/--
[mulByPoly_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma mulByPoly_step
  {f : ℝ → ℂ}
  {k : ℕ} :
-- imply
  (fun x : ℝ => ↑(-2 * Real.pi) * I * ↑x * mulByPoly f k x) = mulByPoly f (k + 1) := by
-- proof
  ext x; unfold mulByPoly; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[mulByPoly_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma mulByPoly_smooth
  {f : ℝ → ℂ}
  {k : ℕ}
-- given
  (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
-- imply
  ContDiff ℝ (↑(⊤ : ℕ∞)) (mulByPoly f k) :=
-- proof
  (contDiff_const.mul Complex.ofRealCLM.contDiff).pow k |>.mul hf

end FourierAnalysis

namespace FourierAnalysis

/--
[mulByPoly_compact_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma mulByPoly_compact_support
  {f : ℝ → ℂ}
  {k : ℕ}
-- given
  (hf : HasCompactSupport f) :
-- imply
  HasCompactSupport (mulByPoly f k) := by
-- proof
  apply hf.mono; intro x hx
  simp only [Function.mem_support, mulByPoly] at hx ⊢
  intro hfx; apply hx; simp [hfx]

end FourierAnalysis

namespace FourierAnalysis

/--
[mulByPoly_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma mulByPoly_integrable
  {f : ℝ → ℂ}
  {k : ℕ}
-- given
  (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hsupp : HasCompactSupport f) :
-- imply
  Integrable (mulByPoly f k) :=
-- proof
  (mulByPoly_smooth f hf k).continuous.integrable_of_hasCompactSupport
    (mulByPoly_compact_support f hsupp k)

end FourierAnalysis

namespace FourierAnalysis

/--
[mulByPoly_x_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma mulByPoly_x_integrable
  {f : ℝ → ℂ}
  {k : ℕ}
-- given
  (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hsupp : HasCompactSupport f) :
-- imply
  Integrable (fun x : ℝ => (x : ℂ) * mulByPoly f k x) := by
-- proof
  apply (Complex.ofRealCLM.continuous.mul
    (mulByPoly_smooth f hf k).continuous).integrable_of_hasCompactSupport
  apply hsupp.mono; intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hfx; apply hx; simp [mulByPoly, hfx] at *

end FourierAnalysis

namespace FourierAnalysis

/--
[iteratedDeriv_fourierTransform](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma iteratedDeriv_fourierTransform
-- imply
  ∀ (k : ℕ) (f : ℝ → ℂ), ContDiff ℝ (↑(⊤ : ℕ∞)) f → HasCompactSupport f → iteratedDeriv k (fourierTransform f) = fourierTransform (mulByPoly f k) := by
-- proof
  intro k; induction k with
  | zero => intro f _ _; simp [iteratedDeriv_zero, mulByPoly_zero]
  | succ k ih =>
    intro f hf_smooth hf_supp
    rw [iteratedDeriv_succ']
    have hf_int : Integrable f := hf_smooth.continuous.integrable_of_hasCompactSupport hf_supp
    have hxf_int : Integrable (fun x : ℝ => (x : ℂ) * f x) := by
      rw [show (fun x : ℝ => (x : ℂ) * f x) = (fun x : ℝ => (x : ℂ) * mulByPoly f 0 x) from by
        simp [mulByPoly_zero]]
      exact mulByPoly_x_integrable f hf_smooth hf_supp 0
    have hderiv : deriv (fourierTransform f) = fourierTransform (mulByPoly f 1) := by
      ext ξ; rw [fourier_deriv_freq f hf_int hxf_int ξ]
      congr 1; rw [← mulByPoly_step f 0, mulByPoly_zero]
    rw [hderiv, ih (mulByPoly f 1) (mulByPoly_smooth f hf_smooth 1)
      (mulByPoly_compact_support f hf_supp 1)]
    congr 1; ext x; unfold mulByPoly; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_ft_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_ft_smooth
  {f : ℝ → ℂ}
-- given
  (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hf_supp : HasCompactSupport f) :
-- imply
  ContDiff ℝ (↑(⊤ : ℕ∞)) (fourierTransform f) := by
-- proof
  rw [fourierTransform_eq_mathlib]
  apply Real.contDiff_fourier (N := ⊤)
  intro n _
  have hcont : Continuous (fun v : ℝ => ‖v‖ ^ n * ‖f v‖) :=
    (continuous_norm.pow n).mul hf_smooth.continuous.norm
  have hsupp : HasCompactSupport (fun v : ℝ => ‖v‖ ^ n * ‖f v‖) := by
    apply hf_supp.norm.mono
    intro x hx; simp only [Function.mem_support] at hx ⊢
    intro hfx; apply hx; simp [hfx]
  exact hcont.integrable_of_hasCompactSupport hsupp

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_rapid_decay_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_rapid_decay_aux
  {N : ℕ} :
-- imply
  ∀ (f : ℝ → ℂ), ContDiff ℝ (↑(⊤ : ℕ∞)) f → HasCompactSupport f → ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖fourierTransform f ξ‖ ≤ C * (1 + |ξ|)⁻¹ ^ N := by
-- proof
  induction N with
  | zero =>
    intro f hf_smooth hf_supp
    have hf_int : Integrable f := hf_smooth.continuous.integrable_of_hasCompactSupport hf_supp
    refine ⟨(∫ x : ℝ, ‖f x‖) + 1, by positivity, fun ξ => ?_⟩
    simp only [pow_zero, mul_one]
    linarith [fourierTransform_bound f hf_int ξ]
  | succ N ih =>
    intro f hf_smooth hf_supp
    have hf_smooth_deriv : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv f) := by
      have h : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ↑(⊤ : ℕ∞) := by decide
      exact h ▸ hf_smooth.deriv'
    have hf_supp_deriv : HasCompactSupport (deriv f) := hf_supp.deriv
    obtain ⟨C₁, hC₁_pos, hC₁⟩ := ih (deriv f) hf_smooth_deriv hf_supp_deriv
    have hf_cont : Continuous f := hf_smooth.continuous
    have hf_int : Integrable f := hf_cont.integrable_of_hasCompactSupport hf_supp
    have hf'_int : Integrable (deriv f) :=
      hf_smooth_deriv.continuous.integrable_of_hasCompactSupport hf_supp_deriv
    have hf_decay : Filter.Tendsto f (Filter.cocompact ℝ) (nhds 0) :=
      hf_supp.is_zero_at_infty
    set A := (∫ x : ℝ, ‖f x‖) + 1
    have hA_pos : 0 < A := by positivity
    have hA_bound : ∀ ξ, ‖fourierTransform f ξ‖ ≤ A := fun ξ =>
      calc ‖fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ := fourierTransform_bound f hf_int ξ
        _ ≤ A := le_add_of_nonneg_right one_pos.le
    set C := max (C₁ / Real.pi) (A * 2 ^ (N + 1)) + 1
    have hC_pos : 0 < C := by
      have : 0 ≤ max (C₁ / Real.pi) (A * 2 ^ (N + 1)) :=
        le_max_of_le_left (div_nonneg hC₁_pos.le Real.pi_pos.le)
      linarith
    refine ⟨C, hC_pos, fun ξ => ?_⟩
    by_cases hξ : |ξ| < 1
    ·
      have hξ_pos : 0 ≤ |ξ| := abs_nonneg ξ
      have h1pξ_pos : (0 : ℝ) < 1 + |ξ| := by linarith
      have hinv_pos : 0 < (1 + |ξ|)⁻¹ := inv_pos.mpr h1pξ_pos
      have h2inv_gt : 1 ≤ 2 * (1 + |ξ|)⁻¹ := by
        rw [show (2 : ℝ) * (1 + |ξ|)⁻¹ = 2 / (1 + |ξ|) from by ring]
        rw [le_div_iff₀ h1pξ_pos]; linarith
      have hpow_ge : 1 ≤ (2 * (1 + |ξ|)⁻¹) ^ (N + 1) := one_le_pow₀ h2inv_gt
      have hA_le : A ≤ A * 2 ^ (N + 1) * (1 + |ξ|)⁻¹ ^ (N + 1) := by
        have := le_mul_of_one_le_right hA_pos.le hpow_ge
        rw [mul_pow] at this; linarith
      calc ‖fourierTransform f ξ‖ ≤ A := hA_bound ξ
        _ ≤ A * 2 ^ (N + 1) * (1 + |ξ|)⁻¹ ^ (N + 1) := hA_le
        _ ≤ C * (1 + |ξ|)⁻¹ ^ (N + 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hinv_pos.le _)
          linarith [le_max_right (C₁ / Real.pi) (A * 2 ^ (N + 1))]
    ·
      simp only [not_lt] at hξ
      have hξ_pos : 0 < |ξ| := lt_of_lt_of_le one_pos hξ
      have h1pξ_pos : (0 : ℝ) < 1 + |ξ| := by linarith
      have hinv_pos : 0 < (1 + |ξ|)⁻¹ := inv_pos.mpr h1pξ_pos
      have hpow_pos : 0 < (1 + |ξ|)⁻¹ ^ N := pow_pos hinv_pos N
      have h2πξ_pos : 0 < 2 * Real.pi * |ξ| := by positivity
      have hnorm_coeff : ‖(↑(2 * Real.pi) * I * ↑ξ : ℂ)‖ = 2 * Real.pi * |ξ| := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
          abs_of_pos (show (0 : ℝ) < 2 from by norm_num),
          abs_of_pos Real.pi_pos]
      have hf_differentiable : Differentiable ℝ f := hf_smooth.differentiable (by decide)
      have hfourier_eq := fourier_of_deriv f hf_int hf'_int hf_decay hf_differentiable ξ
      have hprod_bound : 2 * Real.pi * |ξ| * ‖fourierTransform f ξ‖ ≤
        C₁ * (1 + |ξ|)⁻¹ ^ N := by
        calc 2 * Real.pi * |ξ| * ‖fourierTransform f ξ‖
          = ‖(↑(2 * Real.pi) * I * ↑ξ : ℂ)‖ * ‖fourierTransform f ξ‖ := by
            rw [hnorm_coeff]
          _ = ‖(↑(2 * Real.pi) * I * ↑ξ : ℂ) * fourierTransform f ξ‖ := (norm_mul _ _).symm
          _ = ‖fourierTransform (deriv f) ξ‖ := by rw [hfourier_eq, mul_assoc]
          _ ≤ C₁ * (1 + |ξ|)⁻¹ ^ N := hC₁ ξ
      have hFT_bound : ‖fourierTransform f ξ‖ ≤
        C₁ * (1 + |ξ|)⁻¹ ^ N / (2 * Real.pi * |ξ|) := by
        rwa [le_div_iff₀ h2πξ_pos, mul_comm]
      set p := (1 + |ξ|)⁻¹
      suffices hsuff : C₁ / (2 * Real.pi * |ξ|) ≤ C * p by
        calc ‖fourierTransform f ξ‖
          ≤ C₁ * p ^ N / (2 * Real.pi * |ξ|) := hFT_bound
          _ = C₁ / (2 * Real.pi * |ξ|) * p ^ N := by ring
          _ ≤ C * p * p ^ N := mul_le_mul_of_nonneg_right hsuff hpow_pos.le
          _ = C * (p * p ^ N) := by ring
          _ = C * p ^ (N + 1) := by rw [pow_succ']
      rw [show C * p = C / (1 + |ξ|) from by simp [p, div_eq_mul_inv]]
      rw [div_le_div_iff₀ (by positivity) h1pξ_pos]
      calc C₁ * (1 + |ξ|) ≤ C₁ * (2 * |ξ|) := by
        apply mul_le_mul_of_nonneg_left _ hC₁_pos.le; linarith
        _ = C₁ / Real.pi * (2 * Real.pi * |ξ|) := by field_simp
        _ ≤ C * (2 * Real.pi * |ξ|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc C₁ / Real.pi ≤ max (C₁ / Real.pi) (A * 2 ^ (N + 1)) := le_max_left _ _
            _ ≤ C := le_add_of_nonneg_right one_pos.le

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_rapid_decay](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_rapid_decay
  {f : ℝ → ℂ}
  {N : ℕ}
-- given
  (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hf_supp : HasCompactSupport f) :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖fourierTransform f ξ‖ ≤ C * (1 + |ξ|)⁻¹ ^ N :=
-- proof
  schwartz_rapid_decay_aux N f hf_smooth hf_supp

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_rapid_decay_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_rapid_decay_deriv
  {f : ℝ → ℂ}
  {N k : ℕ}
-- given
  (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hf_supp : HasCompactSupport f) :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖iteratedDeriv k (fourierTransform f) ξ‖ ≤ C * (1 + |ξ|)⁻¹ ^ N := by
-- proof
  rw [iteratedDeriv_fourierTransform k f hf_smooth hf_supp]
  exact schwartz_rapid_decay (mulByPoly f k) (mulByPoly_smooth f hf_smooth k)
    (mulByPoly_compact_support f hf_supp k) N

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_decay_of_compact_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_decay_of_compact_support
  {f : ℝ → ℂ}
-- given
  (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hf_supp : HasCompactSupport f) :
-- imply
  Integrable (fourierTransform f) := by
-- proof
  obtain ⟨C, hC_pos, hC_bound⟩ := schwartz_rapid_decay f hf_smooth hf_supp 2
  apply Integrable.mono
    ((integrable_one_add_norm (show (↑(Module.finrank ℝ ℝ) : ℝ) < 2 from by
      simp [Module.finrank_self])).const_mul C)
    (schwartz_ft_smooth f hf_smooth hf_supp).continuous.aestronglyMeasurable
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC_pos.le
    (Real.rpow_nonneg (by linarith [norm_nonneg ξ]) _))]
  have h_eq : (1 + |ξ|)⁻¹ ^ 2 = (1 + ‖ξ‖) ^ (-(2 : ℝ)) := by
    rw [Real.norm_eq_abs, inv_pow,
      ← Real.rpow_natCast (1 + |ξ|) 2,
      ← Real.rpow_neg (by linarith [abs_nonneg ξ])]; simp
  calc ‖fourierTransform f ξ‖ ≤ C * (1 + |ξ|)⁻¹ ^ 2 := hC_bound ξ
    _ = C * (1 + ‖ξ‖) ^ (-(2 : ℝ)) := by rw [h_eq]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransformND_eq_fourier_bridge_early](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransformND_eq_fourier_bridge_early
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {ξ : Fin n → ℝ} :
-- imply
  fourierTransformND n f ξ = (𝓕 (f ∘ @WithLp.ofLp 2 (Fin n → ℝ))) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin n)) := by
-- proof
  rw [Real.fourier_eq']
  rw [← MeasurePreserving.integral_comp
    (PiLp.volume_preserving_toLp (Fin n))
    ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding)]
  unfold fourierTransformND
  congr 1
  ext x
  simp only [Function.comp, smul_eq_mul, mul_comm (cexp _) (f x)]
  congr 1
  have h_inner : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (WithLp.toLp 2 x) (WithLp.toLp 2 ξ) =
    ∑ i, ξ i * x i := by
    change dotProduct ξ (star x) = _
    simp [dotProduct, star_trivial]
  rw [h_inner]
  push_cast
  ring

end FourierAnalysis

namespace FourierAnalysis

/--
[piNorm_le_euclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma piNorm_le_euclidean
  {n : ℕ}
  {ξ : Fin n → ℝ} :
-- imply
  ‖ξ‖ ≤ ‖(WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin n))‖ := by
-- proof
  rw [EuclideanSpace.norm_eq, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i; rw [Real.norm_eq_abs]
  calc |ξ i| = √(|ξ i| ^ 2) := by rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ √(∑ j : Fin n, ‖ξ j‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      have : |ξ i| = ‖ξ i‖ := (Real.norm_eq_abs _).symm
      rw [this]
      exact Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_FT_partial_IBP_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_FT_partial_IBP_bound
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {N : ℕ}
-- given
  (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hf_supp : HasCompactSupport f) :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ ξ : Fin n → ℝ, ‖fourierTransformND n f ξ‖ ≤ C * (1 + ‖ξ‖)⁻¹ ^ N := by
-- proof
  let E := EuclideanSpace ℝ (Fin n)
  let g : E → ℂ := f ∘ @WithLp.ofLp 2 (Fin n → ℝ)
  have hg_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g :=
    hf_smooth.comp (PiLp.contDiff_ofLp (ι := Fin n) (E := fun _ => ℝ))
  have hg_supp : HasCompactSupport g :=
    hf_supp.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin n => ℝ))
  let φ : SchwartzMap E ℂ := hg_supp.toSchwartzMap hg_smooth
  let ψ : SchwartzMap E ℂ := fourierTransformCLM ℂ φ
  let C_N : ℝ := 2 ^ N * ((Iic (N, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) ψ
  refine ⟨C_N + 1, by positivity, fun ξ => ?_⟩
  rw [fourierTransformND_eq_fourier_bridge_early]
  have hψ_eq : ∀ w, (ψ : E → ℂ) w = 𝓕 g w :=
    fun w => congr_fun (congrArg DFunLike.coe (fourierTransformCLM_apply ℂ φ)) w
  rw [show 𝓕 g (WithLp.toLp 2 ξ) = ψ (WithLp.toLp 2 ξ) from (hψ_eq _).symm]
  set w : E := WithLp.toLp 2 ξ with hw_def
  have h_main := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0))
    (le_refl N) (le_refl 0) ψ w
  simp only [norm_iteratedFDeriv_zero] at h_main
  have h1xi : 0 < (1 + ‖ξ‖) ^ N := pow_pos (by linarith [norm_nonneg ξ]) N
  have h1w : 0 < (1 + ‖w‖) ^ N := pow_pos (by linarith [norm_nonneg w]) N
  have hC_N_nn : 0 ≤ C_N := by positivity
  rw [show (C_N + 1) * (1 + ‖ξ‖)⁻¹ ^ N = (C_N + 1) / (1 + ‖ξ‖) ^ N from by
    rw [inv_pow, div_eq_mul_inv]]
  have h_norm_le : ‖ξ‖ ≤ ‖w‖ := piNorm_le_euclidean ξ
  have h_pow_le : (1 + ‖ξ‖) ^ N ≤ (1 + ‖w‖) ^ N :=
    pow_le_pow_left₀ (by linarith [norm_nonneg ξ]) (by linarith) N
  calc ‖ψ w‖
    ≤ C_N / (1 + ‖w‖) ^ N := by
      rw [le_div_iff₀ h1w]; linarith [mul_comm (‖ψ w‖) ((1 + ‖w‖) ^ N)]
    _ ≤ C_N / (1 + ‖ξ‖) ^ N :=
      div_le_div_of_nonneg_left hC_N_nn h1xi h_pow_le
    _ ≤ (C_N + 1) / (1 + ‖ξ‖) ^ N :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_rapid_decayND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_rapid_decayND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {N : ℕ}
-- given
  (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hf_supp : HasCompactSupport f) :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ ξ : Fin n → ℝ, ‖fourierTransformND n f ξ‖ ≤ C * (1 + ‖ξ‖)⁻¹ ^ N :=
-- proof
  schwartz_FT_partial_IBP_bound f hf_smooth hf_supp N

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_ft_smoothND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_ft_smoothND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
-- given
  (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hf_supp : HasCompactSupport f) :
-- imply
  ContDiff ℝ (↑(⊤ : ℕ∞)) (fourierTransformND n f) := by
-- proof
  let g : EuclideanSpace ℝ (Fin n) → ℂ := f ∘ @WithLp.ofLp 2 (Fin n → ℝ)
  suffices h : ContDiff ℝ (↑(⊤ : ℕ∞)) ((𝓕 g) ∘ (WithLp.toLp 2)) by
    have h_eq : fourierTransformND n f = (𝓕 g) ∘ (WithLp.toLp 2) :=
      funext (fun ξ => fourierTransformND_eq_fourier_bridge_early n f ξ)
    rwa [h_eq]
  apply ContDiff.comp
  · apply Real.contDiff_fourier (N := ⊤)
    intro m _
    have hg_cont : Continuous g :=
      hf_smooth.continuous.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
    have hg_supp : HasCompactSupport g :=
      hf_supp.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin n => ℝ))
    exact (((continuous_norm.pow m).mul hg_cont.norm).integrable_of_hasCompactSupport
      (hg_supp.norm.mono (fun x hx => by
        simp only [Function.mem_support] at hx ⊢
        intro hfx; exact hx (by simp [hfx]))))
  · exact PiLp.contDiff_toLp

end FourierAnalysis

namespace FourierAnalysis

/--
[schwartz_decay_of_compact_supportND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma schwartz_decay_of_compact_supportND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
-- given
  (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
  (hf_supp : HasCompactSupport f) :
-- imply
  Integrable (fourierTransformND n f) := by
-- proof
  obtain ⟨C, hC_pos, hC_bound⟩ := schwartz_rapid_decayND f hf_smooth hf_supp (n + 1)
  have h_finrank : (Module.finrank ℝ (Fin n → ℝ) : ℝ) < (↑(n + 1) : ℝ) := by simp
  have h_int_dom : Integrable (fun ξ : Fin n → ℝ => (1 + ‖ξ‖) ^ (-(↑(n + 1) : ℝ))) :=
    integrable_one_add_norm h_finrank
  apply Integrable.mono (h_int_dom.const_mul C)
    (schwartz_ft_smoothND f hf_smooth hf_supp).continuous.aestronglyMeasurable
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC_pos.le
    (Real.rpow_nonneg (by linarith [norm_nonneg ξ]) _))]
  calc ‖fourierTransformND n f ξ‖
    ≤ C * (1 + ‖ξ‖)⁻¹ ^ (n + 1) := hC_bound ξ
    _ = C * ((1 + ‖ξ‖) ^ (n + 1))⁻¹ := by rw [inv_pow]
    _ = C * (1 + ‖ξ‖) ^ (-(↑(n + 1) : ℝ)) := by
      congr 1
      rw [← Real.rpow_natCast (1 + ‖ξ‖) (n + 1),
        Real.rpow_neg (by linarith [norm_nonneg ξ])]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_gaussian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_gaussian
  {a : ℝ}
  {ξ : ℝ}
-- given
  (ha : 0 < a) :
-- imply
  fourierTransform (fun x => exp (↑(-Real.pi * a * x ^ 2) : ℂ)) ξ = (a : ℂ) ^ (-(1 : ℂ) / 2) * exp (↑(-Real.pi * ξ ^ 2 / a) : ℂ) := by
-- proof
  unfold fourierTransform
  simp_rw [← Complex.exp_add]
  have h1 : ∀ x : ℝ,
    (↑(-Real.pi * a * x ^ 2) : ℂ) + ↑(-2 * Real.pi * ξ * x) * I =
    -(↑(Real.pi * a)) * (↑x + ↑(ξ / a) * I) ^ 2 + ↑(-Real.pi * ξ ^ 2 / a) := by
    intro x
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
    push_cast
    have : (↑x + ↑ξ / ↑a * I : ℂ) ^ 2 =
      ↑x ^ 2 + 2 * ↑x * (↑ξ / ↑a) * I + (↑ξ / ↑a) ^ 2 * I ^ 2 := by ring
    rw [this, I_sq]; field_simp; ring
  simp_rw [h1, Complex.exp_add]
  rw [show (∫ x : ℝ, cexp (-(↑(Real.pi * a)) * (↑x + ↑(ξ / a) * I) ^ 2) *
    cexp (↑(-Real.pi * ξ ^ 2 / a))) =
    (∫ x : ℝ, cexp (-(↑(Real.pi * a)) * (↑x + ↑(ξ / a) * I) ^ 2)) *
      cexp (↑(-Real.pi * ξ ^ 2 / a)) from integral_mul_const _ _]
  have hb : (0 : ℝ) < (↑(Real.pi * a) : ℂ).re := by
    simp only [ofReal_re]; exact mul_pos Real.pi_pos ha
  rw [GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I hb (ξ / a)]
  congr 1
  have h2 : (↑Real.pi / ↑(Real.pi * a) : ℂ) = ↑(1 / a : ℝ) := by push_cast; field_simp
  rw [h2]
  have h12 : (1 : ℂ) / 2 = ↑((1 : ℝ) / 2) := by push_cast; ring
  have hm12 : -(1 : ℂ) / 2 = ↑(-(1 : ℝ) / 2) := by push_cast; ring
  rw [h12, hm12]
  rw [← ofReal_cpow (by positivity : (0 : ℝ) ≤ 1 / a) (1 / 2)]
  rw [← ofReal_cpow (by linarith : (0 : ℝ) ≤ a) (-1 / 2)]
  congr 1
  rw [one_div, Real.inv_rpow (le_of_lt ha)]
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) from by ring]
  rw [Real.rpow_neg (le_of_lt ha)]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_gaussian_real_nD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_gaussian_real_nD
  {n : ℕ}
  {a : ℝ}
  {ξ : Fin n → ℝ}
-- given
  (ha : 0 < a) :
-- imply
  fourierTransformND n (fun x => exp (↑(-Real.pi) * ↑a * ↑(euclidNormSq x))) ξ = (a : ℂ) ^ (-(↑n : ℂ) / 2) * exp (↑(-Real.pi) * ↑(euclidNormSq ξ) / ↑a) := by
-- proof
  unfold fourierTransformND euclidNormSq
  simp_rw [← Complex.exp_add]
  have integrand_eq : ∀ x : Fin n → ℝ,
    (↑(-Real.pi) : ℂ) * ↑a * ↑(∑ i, x i ^ 2) + ↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j) =
    -(↑(Real.pi * a)) * ∑ i, (↑(x i) : ℂ)^2 + ∑ i, (-2 * ↑Real.pi * I * ↑(ξ i)) * ↑(x i) := by
    intro x
    push_cast
    simp only [Finset.mul_sum]
    congr 1
    · ring
    · congr 1; ext i; ring
  simp_rw [integrand_eq]
  have hb : 0 < (↑(Real.pi * a) : ℂ).re := by
    simp only [ofReal_re]; exact mul_pos Real.pi_pos ha
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add hb]
  congr 1
  · have h1 : (↑Real.pi / ↑(Real.pi * a) : ℂ) = (↑a : ℂ)⁻¹ := by
    push_cast; field_simp
    rw [h1, Fintype.card_fin]
    have harg : (↑a : ℂ).arg ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg ha.le]; exact Real.pi_pos.ne
    rw [inv_cpow _ _ harg]
    rw [show (-(↑n : ℂ) / 2 : ℂ) = -(↑n / 2 : ℂ) from by ring]
    rw [cpow_neg]
  · congr 1
    have h_sq : ∀ i : Fin n,
      (-2 * ↑Real.pi * I * ↑(ξ i)) ^ 2 = -4 * ↑Real.pi ^ 2 * ↑(ξ i) ^ 2 := by
      intro i
      rw [show (-2 * ↑Real.pi * I * ↑(ξ i)) ^ 2 =
        4 * ↑Real.pi ^ 2 * I ^ 2 * ↑(ξ i) ^ 2 from by ring]
      rw [I_sq]; ring
    simp_rw [h_sq]
    rw [show (∑ x : Fin n, -4 * (↑Real.pi : ℂ) ^ 2 * ↑(ξ x) ^ 2) =
      -4 * ↑Real.pi ^ 2 * ∑ x, (↑(ξ x) : ℂ) ^ 2 from by rw [Finset.mul_sum]]
    push_cast; field_simp

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_gaussian_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_gaussian_complex
  {n : ℕ}
  {z : ℂ}
  {ξ : Fin n → ℝ}
-- given
  (hz : 0 < z.re)
  (_him : z.im ≠ 0) :
-- imply
  fourierTransformND n (fun x => exp (↑(-Real.pi) * z * ↑(euclidNormSq x))) ξ = z ^ (-(↑n : ℂ) / 2) * exp (↑(-Real.pi) * ↑(euclidNormSq ξ) / z) := by
-- proof
  unfold fourierTransformND euclidNormSq
  simp_rw [← Complex.exp_add]
  have integrand_eq : ∀ x : Fin n → ℝ,
    (↑(-Real.pi) : ℂ) * z * ↑(∑ i, x i ^ 2) + ↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j) =
    -(↑Real.pi * z) * ∑ i, (↑(x i) : ℂ)^2 +
      ∑ i, (-2 * ↑Real.pi * I * ↑(ξ i)) * ↑(x i) := by
    intro x
    push_cast
    simp only [Finset.mul_sum]
    congr 1
    · ring
    · congr 1; ext i; ring
  simp_rw [integrand_eq]
  have hb : 0 < (↑Real.pi * z : ℂ).re := by
    rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_pos Real.pi_pos hz
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add hb]
  congr 1
  · have h1 : (↑Real.pi / (↑Real.pi * z) : ℂ) = z⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)]
    rw [h1, Fintype.card_fin]
    have harg : z.arg ≠ Real.pi := by
      intro h
      rw [arg_eq_pi_iff] at h
      linarith [h.1]
    rw [inv_cpow _ _ harg]
    rw [show (-(↑n : ℂ) / 2 : ℂ) = -(↑n / 2 : ℂ) from by ring]
    rw [cpow_neg]
  · congr 1
    have h_sq : ∀ i : Fin n,
      (-2 * ↑Real.pi * I * ↑(ξ i)) ^ 2 = -4 * ↑Real.pi ^ 2 * ↑(ξ i) ^ 2 := by
      intro i
      rw [show (-2 * ↑Real.pi * I * ↑(ξ i)) ^ 2 =
        4 * ↑Real.pi ^ 2 * I ^ 2 * ↑(ξ i) ^ 2 from by ring]
      rw [I_sq]; ring
    simp_rw [h_sq]
    rw [show (∑ x : Fin n, -4 * (↑Real.pi : ℂ) ^ 2 * ↑(ξ x) ^ 2) =
      -4 * ↑Real.pi ^ 2 * ∑ x, (↑(ξ x) : ℂ) ^ 2 from by rw [Finset.mul_sum]]
    push_cast; field_simp

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_integral_swap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_integral_swap
  {f g : ℝ → ℂ}
-- given
  (hf : Integrable f)
  (hg : Integrable g) :
-- imply
  ∫ x : ℝ, fourierTransform f x * g x = ∫ x : ℝ, f x * fourierTransform g x := by
-- proof
  simp only [fourierTransform]
  have lhs_eq : ∀ x : ℝ, (∫ ξ, f ξ * cexp (↑(-2 * Real.pi * x * ξ) * I)) * g x =
    ∫ ξ, f ξ * g x * cexp (↑(-2 * Real.pi * x * ξ) * I) := by
    intro x
    rw [show (fun ξ => f ξ * g x * cexp (↑(-2 * Real.pi * x * ξ) * I)) =
      (fun ξ => (f ξ * cexp (↑(-2 * Real.pi * x * ξ) * I)) * g x) from by ext; ring]
    exact (integral_mul_const (g x) _).symm
  simp_rw [lhs_eq]
  have rhs_eq : ∀ x : ℝ, f x * (∫ ξ, g ξ * cexp (↑(-2 * Real.pi * x * ξ) * I)) =
    ∫ ξ, f x * g ξ * cexp (↑(-2 * Real.pi * x * ξ) * I) := by
    intro x
    rw [show (fun ξ => f x * g ξ * cexp (↑(-2 * Real.pi * x * ξ) * I)) =
      (fun ξ => f x * (g ξ * cexp (↑(-2 * Real.pi * x * ξ) * I))) from by ext; ring]
    exact (integral_const_mul (f x) _).symm
  simp_rw [rhs_eq]
  rw [integral_integral_swap]
  ·
    congr 1; ext a; congr 1; ext b; ring_nf
  ·
    apply Integrable.mono (hg.mul_prod hf)
    · apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · exact hf.aestronglyMeasurable.comp_snd
        · exact hg.aestronglyMeasurable.comp_fst
      · apply (Complex.continuous_exp.comp ?_).aestronglyMeasurable
        apply Continuous.mul
        · apply Complex.continuous_ofReal.comp
          exact (((continuous_const.mul continuous_const).mul continuous_fst).mul continuous_snd)
        · exact continuous_const
    · apply ae_of_all
      intro ⟨x, ξ⟩
      simp only [Function.uncurry]
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul]
      exact (mul_comm _ _).le

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_inner_swap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_inner_swap
  {f g : ℝ → ℂ}
-- given
  (hf : Integrable f)
  (hg : Integrable g) :
-- imply
  complexL2Inner (fourierTransform f) g = complexL2Inner f (inverseFourierTransform g) := by
-- proof
  unfold complexL2Inner
  have hcg : Integrable (fun x => starRingEnd ℂ (g x)) := by
    apply Integrable.mono hg hg.aestronglyMeasurable.star
    apply ae_of_all; intro x; simp
  rw [fourier_integral_swap f (fun x => starRingEnd ℂ (g x)) hf hcg]
  congr 1; ext x; congr 1
  have h1 := fourier_conj (fun x => starRingEnd ℂ (g x)) hcg x
  simp only [starRingEnd_self_apply] at h1
  rw [← h1]
  simp

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_L2_inner_product_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_L2_inner_product_interaction
  {f g : ℝ → ℂ}
-- given
  (hf : Integrable f)
  (hg : Integrable g) :
-- imply
  (∫ x : ℝ, fourierTransform f x * g x = ∫ x : ℝ, f x * fourierTransform g x) ∧ (complexL2Inner (fourierTransform f) g = complexL2Inner f (inverseFourierTransform g)) :=
-- proof
  ⟨fourier_integral_swap f g hf hg, fourier_inner_swap f g hf hg⟩

end FourierAnalysis

namespace FourierAnalysis

/--
[real_inner_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
private lemma real_inner_eq_mul (a b : ℝ) : @inner ℝ ℝ _ a b = a * b := by
  simp only [inner, Inner.inner, starRingEnd_apply, star_trivial, RCLike.re_to_real, mul_comm]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransform_eq_mathlib_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransform_eq_mathlib_fourier
  {f : ℝ → ℂ}
  {ξ : ℝ} :
-- imply
  fourierTransform f ξ = 𝓕 f ξ := by
-- proof
  unfold fourierTransform
  rw [Real.fourier_eq']
  congr 1; ext v
  rw [smul_eq_mul, mul_comm]; congr 1; congr 1; congr 1; congr 1
  rw [real_inner_eq_mul]; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[inverseFourierTransform_eq_mathlib_fourierInv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma inverseFourierTransform_eq_mathlib_fourierInv
  {f : ℝ → ℂ}
  {x : ℝ} :
-- imply
  inverseFourierTransform f x = 𝓕⁻ f x := by
-- proof
  unfold inverseFourierTransform
  rw [Real.fourierInv_eq']
  congr 1; ext v
  rw [smul_eq_mul, mul_comm]; congr 1; congr 1; congr 1; congr 1
  rw [real_inner_eq_mul]; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_inversion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_inversion
  {f : ℝ → ℂ}
  {x : ℝ}
-- given
  (hf : Integrable f)
  (hf_hat : Integrable (fourierTransform f))
  (hf_cont : Continuous f) :
-- imply
  inverseFourierTransform (fourierTransform f) x = f x := by
-- proof
  rw [inverseFourierTransform_eq_mathlib_fourierInv]
  have hf_hat' : Integrable (𝓕 f) := by
    rwa [show (𝓕 f) = fourierTransform f from
      funext (fun ξ => (fourierTransform_eq_mathlib_fourier f ξ).symm)]
  conv_lhs => rw [show fourierTransform f = 𝓕 f from
    funext (fun ξ => fourierTransform_eq_mathlib_fourier f ξ)]
  exact hf.fourierInv_fourier_eq hf_hat' hf_cont.continuousAt

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_inversion_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_inversion_reverse
  {f : ℝ → ℂ}
  {x : ℝ}
-- given
  (hf : Integrable f)
  (hf_check : Integrable (inverseFourierTransform f))
  (hf_cont : Continuous f) :
-- imply
  fourierTransform (inverseFourierTransform f) x = f x := by
-- proof
  let g : ℝ → ℂ := fun y => f (-y)
  have hg_int : Integrable g := hf.comp_neg
  have hg_cont : Continuous g := hf_cont.comp continuous_neg
  have h_fg : 𝓕 g = 𝓕⁻ f := (Real.fourierInv_eq_fourier_comp_neg f).symm
  have hg_hat : Integrable (𝓕 g) := by
    rw [h_fg]
    rwa [show 𝓕⁻ f = inverseFourierTransform f from
      funext (fun y => (inverseFourierTransform_eq_mathlib_fourierInv f y).symm)]
  have h_inv_g : ∀ y, 𝓕⁻ (𝓕 g) y = g y :=
    fun y => hg_int.fourierInv_fourier_eq hg_hat hg_cont.continuousAt
  rw [h_fg] at h_inv_g
  have h1 := h_inv_g (-x)
  change 𝓕⁻ (𝓕⁻ f) (-x) = f (- -x) at h1
  rw [neg_neg] at h1
  rw [Real.fourierInv_eq_fourier_neg (𝓕⁻ f) (-x)] at h1
  simp only [neg_neg] at h1
  rw [fourierTransform_eq_mathlib_fourier]
  rw [show inverseFourierTransform f = 𝓕⁻ f from
    funext (fun y => inverseFourierTransform_eq_mathlib_fourierInv f y)]
  exact h1

end FourierAnalysis

namespace FourierAnalysis

/--
[plancherel_ft_memLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma plancherel_ft_memLp
  {f : ℝ → ℂ}
-- given
  (hf : Integrable f)
  (hf2 : MeasureTheory.MemLp f 2)
  (hf_hat : Integrable (fourierTransform f))
  (hf_cont : Continuous f) :
-- imply
  MeasureTheory.MemLp (fourierTransform f) 2 := by
-- proof
  rw [memLp_two_iff_integrable_sq_norm hf_hat.aestronglyMeasurable]
  apply Integrable.mono' (hf_hat.norm.const_mul (∫ x, ‖f x‖))
  · exact (hf_hat.aestronglyMeasurable.norm.pow 2).aemeasurable.aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (fourierTransform_bound f hf ξ) (norm_nonneg _)

end FourierAnalysis

namespace FourierAnalysis

/--
[plancherel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma plancherel
  {f g : ℝ → ℂ}
-- given
  (hf : Integrable f)
  (hg : Integrable g)
  (hf2 : MeasureTheory.MemLp f 2)
  (hg2 : MeasureTheory.MemLp g 2)
  (hf_hat : Integrable (fourierTransform f))
  (hg_hat : Integrable (fourierTransform g))
  (hf_cont : Continuous f)
  (hg_cont : Continuous g) :
-- imply
  complexL2Inner (fourierTransform f) (fourierTransform g) = complexL2Inner f g := by
-- proof
  rw [fourier_inner_swap f (fourierTransform g) hf hg_hat]
  congr 1
  ext x
  exact fourier_inversion g hg hg_hat hg_cont x

end FourierAnalysis

namespace FourierAnalysis

/--
[plancherel_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma plancherel_norm
  {f : ℝ → ℂ}
-- given
  (hf : Integrable f)
  (hf2 : MeasureTheory.MemLp f 2)
  (hf_hat : Integrable (fourierTransform f))
  (hf_cont : Continuous f) :
-- imply
  complexL2Inner (fourierTransform f) (fourierTransform f) = complexL2Inner f f :=
-- proof
  plancherel f f hf hf hf2 hf2 hf_hat hf_hat hf_cont hf_cont

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransformND_eq_fourier_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransformND_eq_fourier_bridge
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {ξ : Fin n → ℝ} :
-- imply
  fourierTransformND n f ξ = (𝓕 (f ∘ @WithLp.ofLp 2 (Fin n → ℝ))) (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin n)) := by
-- proof
  rw [Real.fourier_eq']
  rw [← MeasurePreserving.integral_comp
    (PiLp.volume_preserving_toLp (Fin n))
    ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding)]
  unfold fourierTransformND
  congr 1
  ext x
  simp only [Function.comp, smul_eq_mul, mul_comm (cexp _) (f x)]
  congr 1
  have h_inner : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (WithLp.toLp 2 x) (WithLp.toLp 2 ξ) =
    ∑ i, ξ i * x i := by
    change dotProduct ξ (star x) = _
    simp [dotProduct, star_trivial]
  rw [h_inner]
  push_cast
  ring

end FourierAnalysis

namespace FourierAnalysis

/--
[inverseFourierTransformND_eq_fourierInv_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma inverseFourierTransformND_eq_fourierInv_bridge
  {n : ℕ}
  {g : (Fin n → ℝ) → ℂ}
  {x : Fin n → ℝ} :
-- imply
  inverseFourierTransformND n g x = (𝓕⁻ (g ∘ @WithLp.ofLp 2 (Fin n → ℝ))) (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) := by
-- proof
  rw [Real.fourierInv_eq']
  rw [← MeasurePreserving.integral_comp
    (PiLp.volume_preserving_toLp (Fin n))
    ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding)]
  unfold inverseFourierTransformND
  congr 1
  ext ξ
  simp only [Function.comp, smul_eq_mul, mul_comm (cexp _) (g ξ)]
  congr 1
  have h_inner : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (WithLp.toLp 2 ξ) (WithLp.toLp 2 x) =
    ∑ i, ξ i * x i := by
    change dotProduct x (star ξ) = _
    simp [dotProduct, star_trivial, mul_comm]
  rw [h_inner]
  push_cast
  ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_inversionND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_inversionND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {x : Fin n → ℝ}
-- given
  (hf : Integrable f)
  (hf_hat : Integrable (fourierTransformND n f))
  (hf_cont : Continuous f) :
-- imply
  inverseFourierTransformND n (fourierTransformND n f) x = f x := by
-- proof
  let g : EuclideanSpace ℝ (Fin n) → ℂ := f ∘ @WithLp.ofLp 2 (Fin n → ℝ)
  have hg_int : Integrable g :=
    ((PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding).mpr hf
  have hFg_int : Integrable (𝓕 g) := by
    have h_eq : fourierTransformND n f = (𝓕 g) ∘ (WithLp.toLp 2) :=
      funext (fun ξ => fourierTransformND_eq_fourier_bridge n f ξ)
    rw [h_eq] at hf_hat
    exact ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding).mp hf_hat
  have hg_cont : Continuous g := hf_cont.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
  have h_inv := hg_int.fourierInv_fourier_eq hFg_int
    (v := WithLp.toLp 2 x) hg_cont.continuousAt
  rw [inverseFourierTransformND_eq_fourierInv_bridge]
  have h_comp : (fourierTransformND n f) ∘ @WithLp.ofLp 2 (Fin n → ℝ) = 𝓕 g := by
    funext ξ
    show fourierTransformND n f (WithLp.ofLp ξ) = 𝓕 g ξ
    rw [fourierTransformND_eq_fourier_bridge]
  rwa [h_comp]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_integral_swapND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_integral_swapND
  {n : ℕ}
  {f g : (Fin n → ℝ) → ℂ}
-- given
  (hf : Integrable f)
  (hg : Integrable g) :
-- imply
  ∫ x, fourierTransformND n f x * g x = ∫ x, f x * fourierTransformND n g x := by
-- proof
  simp only [fourierTransformND]
  have lhs_eq : ∀ x : Fin n → ℝ,
    (∫ ξ, f ξ * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, x j * ξ j))) * g x =
    ∫ ξ, f ξ * g x * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, x j * ξ j)) := by
    intro x
    rw [show (fun ξ => f ξ * g x * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, x j * ξ j))) =
      (fun ξ => (f ξ * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, x j * ξ j))) * g x) from by ext; ring]
    exact (integral_mul_const (g x) _).symm
  simp_rw [lhs_eq]
  have rhs_eq : ∀ x : Fin n → ℝ,
    f x * (∫ ξ, g ξ * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, x j * ξ j))) =
    ∫ ξ, f x * g ξ * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, x j * ξ j)) := by
    intro x
    rw [show (fun ξ => f x * g ξ * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, x j * ξ j))) =
      (fun ξ => f x * (g ξ * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, x j * ξ j)))) from by ext; ring]
    exact (integral_const_mul (f x) _).symm
  simp_rw [rhs_eq]
  rw [integral_integral_swap]
  ·
    congr 1; ext a; congr 1; ext b
    congr 1; congr 1; congr 1; congr 1
    exact Finset.sum_congr rfl (fun i _ => mul_comm (b i) (a i))
  ·
    apply Integrable.mono (hg.mul_prod hf)
    · apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · exact hf.aestronglyMeasurable.comp_snd
        · exact hg.aestronglyMeasurable.comp_fst
      · apply (Complex.continuous_exp.comp ?_).aestronglyMeasurable
        apply Continuous.mul
        · exact continuous_const
        · exact Complex.continuous_ofReal.comp
          (continuous_finset_sum _ (fun j _ =>
            ((continuous_apply j).comp continuous_fst).mul
            ((continuous_apply j).comp continuous_snd)))
    · apply ae_of_all
      intro ⟨x, ξ⟩
      simp only [Function.uncurry]
      rw [norm_mul, norm_mul,
        show (↑(-2 * Real.pi) : ℂ) * I * (↑(∑ j, x j * ξ j) : ℂ) =
          (↑(-2 * Real.pi * ∑ j, x j * ξ j) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul]
      exact (mul_comm _ _).le

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_conjND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_conjND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {ξ : Fin n → ℝ}
-- given
  (hf : Integrable f) :
-- imply
  starRingEnd ℂ (fourierTransformND n f ξ) = inverseFourierTransformND n (fun x => starRingEnd ℂ (f x)) ξ := by
-- proof
  unfold fourierTransformND inverseFourierTransformND
  have h1 : (starRingEnd ℂ) (∫ x, f x * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j))) =
    ∫ x, (starRingEnd ℂ) (f x * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j))) :=
    (integral_conj (𝕜 := ℂ)
      (f := fun x => f x * cexp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j)))).symm
  rw [h1]
  congr 1; ext x
  rw [map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have : (∑ j : Fin n, ξ j * x j) = (∑ j : Fin n, x j * ξ j) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [this]; push_cast; ring

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_inner_swapND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_inner_swapND
  {n : ℕ}
  {f g : (Fin n → ℝ) → ℂ}
-- given
  (hf : Integrable f)
  (hg : Integrable g) :
-- imply
  complexL2InnerND (fourierTransformND n f) g = complexL2InnerND f (inverseFourierTransformND n g) := by
-- proof
  unfold complexL2InnerND
  have hcg : Integrable (fun x => starRingEnd ℂ (g x)) := by
    apply Integrable.mono hg hg.aestronglyMeasurable.star
    apply ae_of_all; intro x; simp
  rw [fourier_integral_swapND f (fun x => starRingEnd ℂ (g x)) hf hcg]
  congr 1; ext x; congr 1
  have h1 := fourier_conjND (fun x => starRingEnd ℂ (g x)) hcg x
  simp only [starRingEnd_self_apply] at h1
  rw [← h1]
  simp

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransformND_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransformND_bound
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {ξ : Fin n → ℝ}
-- given
  (hf : Integrable f) :
-- imply
  ‖fourierTransformND n f ξ‖ ≤ ∫ x, ‖f x‖ := by
-- proof
  unfold fourierTransformND
  calc ‖∫ x, f x * exp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j))‖
    ≤ ∫ x, ‖f x * exp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ := by
      congr 1; ext x
      rw [norm_mul]
      have : ‖exp (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j))‖ = 1 := by
        rw [show (↑(-2 * Real.pi) * I * ↑(∑ j, ξ j * x j) : ℂ) =
          ↑((-2 * Real.pi) * (∑ j, ξ j * x j)) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [this, mul_one]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransformND_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransformND_continuous
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
-- given
  (hf : Integrable f) :
-- imply
  Continuous (fourierTransformND n f) := by
-- proof
  let g : EuclideanSpace ℝ (Fin n) → ℂ := f ∘ @WithLp.ofLp 2 (Fin n → ℝ)
  have h_eq : fourierTransformND n f = (𝓕 g) ∘ (WithLp.toLp 2) :=
    funext (fun ξ => fourierTransformND_eq_fourier_bridge n f ξ)
  rw [h_eq]
  have hg_int : Integrable g :=
    ((PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding).mpr hf
  have hFg_cont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg_int
  exact hFg_cont.comp (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))

end FourierAnalysis

namespace FourierAnalysis

/--
[fourierTransformND_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourierTransformND_tendsto_zero
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
-- given
  (_hf : Integrable f) :
-- imply
  Filter.Tendsto (fourierTransformND n f) (Filter.cocompact (Fin n → ℝ)) (nhds 0) := by
-- proof
  let g : EuclideanSpace ℝ (Fin n) → ℂ := f ∘ @WithLp.ofLp 2 (Fin n → ℝ)
  have h_eq : fourierTransformND n f = (𝓕 g) ∘ (WithLp.toLp 2) :=
    funext (fun ξ => fourierTransformND_eq_fourier_bridge n f ξ)
  rw [h_eq]
  exact (tendsto_integral_exp_inner_smul_cocompact g).comp
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.toCocompactMap.cocompact_tendsto'

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_L1_properties_nD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma fourier_L1_properties_nD
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
-- given
  (hf : Integrable f) :
-- imply
  (∀ ξ, ‖fourierTransformND n f ξ‖ ≤ ∫ x, ‖f x‖) ∧ Continuous (fourierTransformND n f) ∧ Filter.Tendsto (fourierTransformND n f) (Filter.cocompact (Fin n → ℝ)) (nhds 0) :=
-- proof
  ⟨fourierTransformND_bound f hf,
    fourierTransformND_continuous f hf,
    fourierTransformND_tendsto_zero f hf⟩

end FourierAnalysis

namespace FourierAnalysis

/--
[plancherel_ft_memLpND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma plancherel_ft_memLpND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
-- given
  (hf : Integrable f)
  (hf2 : MeasureTheory.MemLp f 2)
  (hf_hat : Integrable (fourierTransformND n f))
  (hf_cont : Continuous f) :
-- imply
  MeasureTheory.MemLp (fourierTransformND n f) 2 := by
-- proof
  rw [memLp_two_iff_integrable_sq_norm hf_hat.aestronglyMeasurable]
  apply Integrable.mono' (hf_hat.norm.const_mul (∫ x, ‖f x‖))
  · exact (hf_hat.aestronglyMeasurable.norm.pow 2).aemeasurable.aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (fourierTransformND_bound f hf ξ) (norm_nonneg _)

end FourierAnalysis

namespace FourierAnalysis

/--
[plancherelND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma plancherelND
  {n : ℕ}
  {f g : (Fin n → ℝ) → ℂ}
-- given
  (hf : Integrable f)
  (hg : Integrable g)
  (hf2 : MeasureTheory.MemLp f 2)
  (hg2 : MeasureTheory.MemLp g 2)
  (hf_hat : Integrable (fourierTransformND n f))
  (hg_hat : Integrable (fourierTransformND n g))
  (hf_cont : Continuous f)
  (hg_cont : Continuous g) :
-- imply
  complexL2InnerND (fourierTransformND n f) (fourierTransformND n g) = complexL2InnerND f g := by
-- proof
  rw [fourier_inner_swapND f (fourierTransformND n g) hf hg_hat]
  congr 1
  ext x
  exact fourier_inversionND n g hg hg_hat hg_cont x

end FourierAnalysis

namespace FourierAnalysis

/--
[plancherel_normND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma plancherel_normND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
-- given
  (hf : Integrable f)
  (hf2 : MeasureTheory.MemLp f 2)
  (hf_hat : Integrable (fourierTransformND n f))
  (hf_cont : Continuous f) :
-- imply
  complexL2InnerND (fourierTransformND n f) (fourierTransformND n f) = complexL2InnerND f f :=
-- proof
  plancherelND n f f hf hf hf2 hf2 hf_hat hf_hat hf_cont hf_cont

end FourierAnalysis

namespace FourierAnalysis

/--
[plancherel_theorem_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean)
-/
@[path]
lemma plancherel_theorem_full
  {n : ℕ}
  {f g : (Fin n → ℝ) → ℂ}
-- given
  (hf : Integrable f)
  (hg : Integrable g)
  (hf_cont : Continuous f)
  (hg_cont : Continuous g)
  (hf2 : MeasureTheory.MemLp f 2 volume)
  (hg2 : MeasureTheory.MemLp g 2 volume)
  (hf_hat : Integrable (fourierTransformND n f))
  (hg_hat : Integrable (fourierTransformND n g)) :
-- imply
  (MeasureTheory.MemLp (fourierTransformND n f) 2 volume) ∧ (MeasureTheory.MemLp (fourierTransformND n g) 2 volume) ∧ (complexL2InnerND (fourierTransformND n f) (fourierTransformND n g) = complexL2InnerND f g) ∧ (complexL2InnerND (fourierTransformND n f) (fourierTransformND n f) = complexL2InnerND f f) :=
-- proof
  ⟨plancherel_ft_memLpND n f hf hf2 hf_hat hf_cont,
    plancherel_ft_memLpND n g hg hg2 hg_hat hg_cont,
    plancherelND n f g hf hg hf2 hg2 hf_hat hg_hat hf_cont hg_cont,
    plancherelND n f f hf hf hf2 hf2 hf_hat hf_hat hf_cont hf_cont⟩
/-- Proposition 2.0.2: for $f \in C_c^{\infty}(\mathbb{R}^n)$, $\hat{f}$ is smooth, rapidly
decaying at infinity together with all its derivatives, and lies in $L^1$. -/
end FourierAnalysis
namespace CM16
export FourierAnalysis (MultiIndex MultiIndex.order multiIndexMonomial iteratedPartialDeriv
  multiIndexDeriv IsCk IsC0 supNorm fourierTransform inverseFourierTransform
  complexL2Inner complexL2Norm complexL2InnerND complexL2NormND translate
  complexConvolution complexConvolutionND fourierTransformND inverseFourierTransformND
  euclidNormSq translateFn fourierTransform_bound fourierTransform_continuous
  fourier_translate fourier_modulate fourier_dilation fourier_convolution
  fourier_deriv_freq fourier_of_deriv fourier_conj fourier_reverse_conj
  fourierTransform_eq_mathlib mulByPoly mulByPoly_zero mulByPoly_step
  mulByPoly_smooth mulByPoly_compact_support mulByPoly_integrable mulByPoly_x_integrable
  iteratedDeriv_fourierTransform schwartz_ft_smooth schwartz_rapid_decay_aux
  schwartz_rapid_decay schwartz_rapid_decay_deriv schwartz_decay_of_compact_support
  schwartz_FT_partial_IBP_bound ft_deriv_eq_ft_mulND ft_contDiff_of_moments_integrableND
  schwartz_rapid_decayND schwartz_rapid_decay_derivND
  schwartz_ft_smoothND schwartz_decay_of_compact_supportND
  fourier_gaussian fourier_gaussian_real_nD fourier_gaussian_complex
  fourier_integral_swap fourier_inner_swap fourier_L2_inner_product_interaction
  fourierTransform_eq_mathlib_fourier inverseFourierTransform_eq_mathlib_fourierInv
  fourier_inversion fourier_inversion_reverse
  plancherel_ft_memLp plancherel plancherel_norm
  fourierTransformND_eq_fourier_bridge inverseFourierTransformND_eq_fourierInv_bridge
  fourier_inversionND fourier_integral_swapND fourier_conjND fourier_inner_swapND
  fourierTransformND_bound fourierTransformND_continuous
  fourierTransformND_tendsto_zero fourier_L1_properties_nD
  plancherel_ft_memLpND plancherelND plancherel_normND
  proposition_2_0_2
  fourier_translateND fourier_modulateND fourier_dilationND fourier_convolutionND
  ft_of_derivND multiIndexMonomial_mul_smooth_compact fourier_reverse_conjND
  fourier_transform_properties
  iteratedPartialDeriv_succ_apply iteratedPartialDeriv_differentiable
  fourierTransformND_iteratedPartialDeriv
  iteratedPartialDeriv_fourierTransformND
  plancherel_theorem_full)
end CM16



-- created on 2026-10-23
