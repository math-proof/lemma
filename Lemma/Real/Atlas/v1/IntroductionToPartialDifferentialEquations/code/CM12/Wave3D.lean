import Mathlib
import sympy.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM12.Wave3D.Part2
open Matrix Real MeasureTheory Filter intervalIntegral WaveEquation3D


namespace WaveEquation3D

/--
[integral_sin_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma integral_sin_eq_two
-- imply
  ∫ θ in (0 : ℝ)..π, sin θ = 2 := by
-- proof
  rw [integral_sin]; simp [Real.cos_pi, Real.cos_zero]; ring

end WaveEquation3D

namespace WaveEquation3D

/--
[sphericalMean_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma sphericalMean_at_zero
  {x : E3}
-- given
  (h : E3 → ℝ) :
-- imply
  SphericalMean h x 0 = h x := by
-- proof
  unfold SphericalMean; simp only [zero_smul, add_zero]
  simp_rw [show ∀ (θ : ℝ), ∫ φ in (0 : ℝ)..(2 * π), h x * sin θ =
    h x * sin θ * (2 * π) from fun θ => by
      rw [intervalIntegral.integral_const]; simp [smul_eq_mul]; ring]
  rw [show (fun θ => h x * sin θ * (2 * π)) = (fun θ => h x * (2 * π) * sin θ) from by ext; ring]
  rw [intervalIntegral.integral_const_mul, integral_sin_eq_two]
  have hpi : (4 : ℝ) * π ≠ 0 := by positivity
  field_simp; ring

end WaveEquation3D

namespace WaveEquation3D

/--
[sphericalToCart_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma sphericalToCart_continuous
-- imply
  Continuous (fun p : (ℝ × ℝ) × ℝ => (EuclideanSpace.equiv (Fin 3) ℝ).symm ![sin p.1.2 * cos p.2, sin p.1.2 * sin p.2, cos p.1.2]) := by
-- proof
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (continuous_sin.comp (continuous_snd.comp continuous_fst)).mul
    (continuous_cos.comp continuous_snd)
  · exact (continuous_sin.comp (continuous_snd.comp continuous_fst)).mul
    (continuous_sin.comp continuous_snd)
  · exact continuous_cos.comp (continuous_snd.comp continuous_fst)

end WaveEquation3D

namespace WaveEquation3D

/--
[sphericalMean_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma sphericalMean_continuous
  {x : E3}
-- given
  (h : E3 → ℝ)
  (hh : Continuous h) :
-- imply
  Continuous (fun r => SphericalMean h x r) := by
-- proof
  unfold SphericalMean
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
  apply Continuous.mul
  · exact hh.comp (continuous_const.add ((continuous_fst.comp continuous_fst).smul
    sphericalToCart_continuous))
  · exact continuous_sin.comp (continuous_snd.comp continuous_fst)

end WaveEquation3D

namespace WaveEquation3D

/--
[SphericalMean_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma SphericalMean_eq
  {x : E3}
  {r : ℝ}
-- given
  (h : E3 → ℝ) :
-- imply
  SphericalMean h x r = (1 / (4 * π)) * ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π), h (x + r • sphericalToCart θ φ) * sin θ :=
-- proof
  rfl
attribute [irreducible] SphericalMean

end WaveEquation3D

namespace WaveEquation3D

/--
[iteratedDeriv_two_mul_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma iteratedDeriv_two_mul_id
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (hf : ContDiff ℝ 2 f) :
-- imply
  iteratedDeriv 2 (fun ρ => ρ * f ρ) x = x * iteratedDeriv 2 f x + 2 * deriv f x := by
-- proof
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hf' : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hf'' : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have h1 : ∀ y, HasDerivAt (fun ρ => ρ * f ρ) (f y + y * deriv f y) y := by
    intro y
    have h := (hasDerivAt_id y).mul (hf'.differentiableAt.hasDerivAt)
    convert h using 1; simp
  have h1_eq : ∀ y, deriv (fun ρ => ρ * f ρ) y = f y + y * deriv f y :=
    fun y => (h1 y).deriv
  have h2 : HasDerivAt (fun y => f y + y * deriv f y)
    (deriv f x + (deriv f x + x * deriv (deriv f) x)) x := by
    exact (hf'.differentiableAt.hasDerivAt).add (by
      have h := (hasDerivAt_id x).mul (hf''.differentiableAt.hasDerivAt)
      convert h using 1; simp)
  have : deriv (deriv fun ρ => ρ * f ρ) x = deriv (fun y => f y + y * deriv f y) x := by
    congr 1; exact funext h1_eq
  rw [this, h2.deriv]; ring

end WaveEquation3D

namespace WaveEquation3D

/--
[sphericalMean_limit_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma sphericalMean_limit_zero
  {x : E3}
-- given
  (h : E3 → ℝ)
  (hh : Continuous h) :
-- imply
  Tendsto (fun r => SphericalMean h x r) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h x)) := by
-- proof
  rw [← sphericalMean_at_zero h x]
  exact ((sphericalMean_continuous h hh x).continuousAt).continuousWithinAt.tendsto

end WaveEquation3D

namespace WaveEquation3D

/--
[dalembert_halfline_representation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma dalembert_halfline_representation
  {w : ℝ → ℝ → ℝ}
  {F G : ℝ → ℝ}
  {t r : ℝ}
-- given
  (hF : ContDiff ℝ 2 F)
  (hG : ContDiff ℝ 1 G)
  (hF0 : F 0 = 0)
  (hG0 : G 0 = 0)
  (hw_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => w p.1 p.2))
  (hw_wave : ∀ t r : ℝ, 0 ≤ r → deriv (fun t' => deriv (fun t'' => w t'' r) t') t = deriv (fun r' => deriv (fun r'' => w t r'') r') r)
  (hw_boundary : ∀ t : ℝ, w t 0 = 0)
  (hw_initial_pos : ∀ r : ℝ, 0 ≤ r → w 0 r = F r)
  (hw_initial_vel : ∀ r : ℝ, 0 < r → HasDerivAt (fun t => w t r) (G r) 0)
  (ht : 0 ≤ t)
  (hr : 0 ≤ r)
  (hrt : r ≤ t) :
-- imply
  w t r = (1 / 2) * (F (r + t) - F (t - r)) + (1 / 2) * ∫ ρ in (t - r)..(r + t), G ρ := by
-- proof
  have h_uniq := WaveEquation1D.dAlembert_halfline_uniqueness F G w hF.contDiffOn hG.contDiffOn hF0 hG0
    hw_reg.contDiffOn (fun t r _ht hr => hw_wave t r hr) hw_boundary hw_initial_pos hw_initial_vel
  have hw_eq := h_uniq t r ht hr
  have h_formula := WaveEquation1D.dAlembert_halfline_formula_xtle F G hF.contDiffOn hG.contDiffOn hF0 hG0 t r ht hr hrt
  rw [hw_eq, h_formula]
  ring

end WaveEquation3D

namespace WaveEquation3D

/--
[sphere_integral_eq_area_times_mean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma sphere_integral_eq_area_times_mean
  {x : E3}
  {r : ℝ}
-- given
  (h : E3 → ℝ) :
-- imply
  SphereIntegral h x r = 4 * π * r ^ 2 * SphericalMean h x r := by
-- proof
  rfl

end WaveEquation3D

namespace WaveEquation3D

/--
[sphericalMean_normal_deriv_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma sphericalMean_normal_deriv_relation
  {f : E3 → ℝ}
  {x : E3}
  {t : ℝ}
-- given
  (_ht : 0 < t) :
-- imply
  SphereIntegralNormalDeriv f x t = 4 * π * t ^ 2 * deriv (fun r => SphericalMean f x r) t := by
-- proof
  rfl

end WaveEquation3D

namespace WaveEquation3D

/--
[symmetric_derivative_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma symmetric_derivative_tendsto
  {f : ℝ → ℝ}
  {t d : ℝ}
-- given
  (hf : HasDerivAt f d t) :
-- imply
  Tendsto (fun h => (f (t + h) - f (t - h)) / (2 * h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
-- proof
  have hfwd : Tendsto (fun h => h⁻¹ • (f (t + h) - f t))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
    hf.tendsto_slope_zero_right
  have hbwd_left : Tendsto (fun s => s⁻¹ • (f (t + s) - f t))
    (nhdsWithin 0 (Set.Iio 0)) (nhds d) :=
    hf.tendsto_slope_zero_left
  have hmap : Tendsto (fun h : ℝ => -h) (nhdsWithin (0:ℝ) (Set.Ioi 0))
    (nhdsWithin 0 (Set.Iio 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (by simpa using continuous_neg.tendsto (0 : ℝ) :
      Tendsto (fun h : ℝ => -h) (nhds 0) (nhds 0)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      simp [Set.mem_Iio, hh]
  have hbwd : Tendsto (fun h => (-h)⁻¹ • (f (t + (-h)) - f t))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
    hbwd_left.comp hmap
  have hbwd' : Tendsto (fun h => h⁻¹ • (f t - f (t - h)))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
    have : (fun h => h⁻¹ • (f t - f (t - h))) =
      (fun h => (-h)⁻¹ • (f (t + (-h)) - f t)) := by
      ext h; simp [inv_neg, smul_eq_mul, sub_eq_add_neg]; ring
    rw [this]; exact hbwd
  have hsum : Tendsto (fun h => h⁻¹ • (f (t + h) - f t) + h⁻¹ • (f t - f (t - h)))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (d + d)) :=
    hfwd.add hbwd'
  have hdiv : Tendsto (fun h => (h⁻¹ • (f (t + h) - f t) + h⁻¹ • (f t - f (t - h))) / 2)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds ((d + d) / 2)) :=
    hsum.div_const 2
  rw [show (d + d) / 2 = d from by ring] at hdiv
  exact hdiv.congr (fun h => by
    simp [smul_eq_mul]
    by_cases hh : h = 0
    · simp [hh]
    · field_simp; ring)

end WaveEquation3D

namespace WaveEquation3D

/--
[integral_average_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma integral_average_tendsto
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : Continuous g) :
-- imply
  Tendsto (fun h => (∫ ρ in (t - h)..(h + t), g ρ) / (2 * h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g t)) := by
-- proof
  let G : ℝ → ℝ := fun u => ∫ x in t..u, g x
  have hG : HasDerivAt G (g t) t :=
    integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have heqf : (fun h => (∫ ρ in (t - h)..(h + t), g ρ) / (2 * h)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
    (fun h => (G (t + h) - G (t - h)) / (2 * h)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    congr 1
    show (∫ ρ in (t - h)..(h + t), g ρ) = G (t + h) - G (t - h)
    have h1 : IntervalIntegrable g volume (t - h) t := hg.intervalIntegrable _ _
    have h2 : IntervalIntegrable g volume t (t + h) := hg.intervalIntegrable _ _
    rw [show h + t = t + h from by ring]
    rw [← integral_add_adjacent_intervals h1 h2]
    rw [integral_symm t (t - h)]
    ring
  rw [Filter.tendsto_congr' heqf]
  exact symmetric_derivative_tendsto G t (g t) hG

end WaveEquation3D

namespace WaveEquation3D

/--
[contDiff_sphericalToCart_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma contDiff_sphericalToCart_pair
-- imply
  ContDiff ℝ ⊤ (fun p : ℝ × ℝ => sphericalToCart p.1 p.2) := by
-- proof
  unfold sphericalToCart
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (contDiff_sin.comp contDiff_fst).mul (contDiff_cos.comp contDiff_snd)
  · exact (contDiff_sin.comp contDiff_fst).mul (contDiff_sin.comp contDiff_snd)
  · exact contDiff_cos.comp contDiff_fst

end WaveEquation3D

namespace WaveEquation3D

/--
[G_tilde_equals_sphere_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma G_tilde_equals_sphere_integral
  {data : CauchyData3D}
  {t : ℝ}
  {x : E3}
-- given
  (ht : 0 < t) :
-- imply
  G_tilde data t x = (1 / (4 * π * t)) * SphereIntegral data.g x t := by
-- proof
  unfold G_tilde
  rw [sphere_integral_eq_area_times_mean]
  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt ht
  field_simp

end WaveEquation3D

namespace WaveEquation3D

/--
[sphericalAverage_tilde_initial_position](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma sphericalAverage_tilde_initial_position
  {data : CauchyData3D}
  {u : ℝ → E3 → ℝ}
  {r : ℝ}
  {x : E3}
-- given
  (_hu : IsWaveSolution3D u)
  (hf : ∀ x, u 0 x = data.f x)
  (_hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
  (_hr : 0 < r) :
-- imply
  sphericalAverage_tilde u 0 r x = F_tilde data r x := by
-- proof
  unfold sphericalAverage_tilde sphericalAverage F_tilde
  congr 1
  congr 1
  ext y
  exact hf y

end WaveEquation3D

namespace WaveEquation3D

/--
[minkowskiInner_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma minkowskiInner_comm
  {n : ℕ}
  {X Y : Fin (n + 1) → ℝ} :
-- imply
  minkowskiInner n X Y = minkowskiInner n Y X := by
-- proof
  simp only [minkowskiInner, minkowskiMetric, dotProduct, mulVec, of_apply]
  simp [mul_comm]

end WaveEquation3D

namespace WaveEquation3D

/--
[lorentz_preserves_inner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma lorentz_preserves_inner
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X Y : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ) :
-- imply
  minkowskiInner n (Λ *ᵥ X) (Λ *ᵥ Y) = minkowskiInner n X Y := by
-- proof
  simp only [minkowskiInner]
  rw [mulVec_mulVec]
  rw [dotProduct_mulVec (Λ *ᵥ X) (minkowskiMetric n * Λ) Y]
  rw [vecMul_mulVec Λ (minkowskiMetric n * Λ) X]
  rw [← Matrix.mul_assoc, hΛ]
  rw [← dotProduct_mulVec]

end WaveEquation3D

namespace WaveEquation3D

/--
[lorentz_preserves_timelike](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma lorentz_preserves_timelike
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ)
  (hX : IsTimelike n X) :
-- imply
  IsTimelike n (Λ *ᵥ X) := by
-- proof
  unfold IsTimelike at *
  rwa [lorentz_preserves_inner hΛ]

end WaveEquation3D

namespace WaveEquation3D

/--
[lorentz_preserves_spacelike](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma lorentz_preserves_spacelike
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ)
  (hX : IsSpacelike n X) :
-- imply
  IsSpacelike n (Λ *ᵥ X) := by
-- proof
  unfold IsSpacelike at *
  rwa [lorentz_preserves_inner hΛ]

end WaveEquation3D

namespace WaveEquation3D

/--
[lorentz_preserves_null](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma lorentz_preserves_null
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ)
  (hX : IsNull n X) :
-- imply
  IsNull n (Λ *ᵥ X) := by
-- proof
  unfold IsNull at *
  rwa [lorentz_preserves_inner hΛ]

end WaveEquation3D

namespace WaveEquation3D

/--
[lorentz_preserves_causal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma lorentz_preserves_causal
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ)
  (hX : IsCausal n X) :
-- imply
  IsCausal n (Λ *ᵥ X) := by
-- proof
  unfold IsCausal at *
  rwa [lorentz_preserves_inner hΛ]

end WaveEquation3D

namespace WaveEquation3D

/--
[nullFrame_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma nullFrame_decomposition
  {n : ℕ}
  {nf : NullFrame n}
  {X Y : Fin (n + 1) → ℝ} :
-- imply
  minkowskiInner n X Y = -(1 / 2) * minkowskiInner n nf.L X * minkowskiInner n nf.Lb Y - (1 / 2) * minkowskiInner n nf.Lb X * minkowskiInner n nf.L Y + angularMetric n nf X Y := by
-- proof
  conv_lhs => rw [nf.completeness X]
  simp only [minkowskiInner, angularMetric]
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct]
  rw [sum_dotProduct (Finset.univ)
    (fun i => (dotProduct (nf.e i) (minkowskiMetric n *ᵥ X)) • nf.e i)]
  simp only [smul_dotProduct, smul_eq_mul]
  ring

end WaveEquation3D

namespace WaveEquation3D

/--
[angularMetric_vanish_L](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma angularMetric_vanish_L
  {n : ℕ}
  {nf : NullFrame n}
  {Y : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf nf.L Y = 0 := by
-- proof
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.L = 0 := by
    rw [minkowskiInner_comm]; exact nf.L_e_orthog i
  simp [h]

end WaveEquation3D

namespace WaveEquation3D

/--
[angularMetric_vanish_Lb](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma angularMetric_vanish_Lb
  {n : ℕ}
  {nf : NullFrame n}
  {Y : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf nf.Lb Y = 0 := by
-- proof
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.Lb = 0 := by
    rw [minkowskiInner_comm]; exact nf.Lb_e_orthog i
  simp [h]

end WaveEquation3D

namespace WaveEquation3D

/--
[angularMetric_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma angularMetric_comm
  {n : ℕ}
  {nf : NullFrame n}
  {X Y : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf X Y = angularMetric n nf Y X := by
-- proof
  simp only [angularMetric]
  congr 1; ext i; ring

end WaveEquation3D

namespace WaveEquation3D

/--
[angularMetric_vanish_L_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma angularMetric_vanish_L_right
  {n : ℕ}
  {nf : NullFrame n}
  {X : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf X nf.L = 0 := by
-- proof
  rw [angularMetric_comm]; exact angularMetric_vanish_L nf X

end WaveEquation3D

namespace WaveEquation3D

/--
[angularMetric_vanish_Lb_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma angularMetric_vanish_Lb_right
  {n : ℕ}
  {nf : NullFrame n}
  {X : Fin (n + 1) → ℝ} :
-- imply
  angularMetric n nf X nf.Lb = 0 := by
-- proof
  rw [angularMetric_comm]; exact angularMetric_vanish_Lb nf X

end WaveEquation3D

namespace WaveEquation3D

/--
[angularMetric_on_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma angularMetric_on_e
  {n : ℕ}
  {nf : NullFrame n}
  {i j : Fin (n - 1)} :
-- imply
  angularMetric n nf (nf.e i) (nf.e j) = if i = j then 1 else 0 := by
-- proof
  simp only [angularMetric, nf.e_orthonormal]
  by_cases h : i = j
  · subst h
    simp [Finset.sum_ite_eq']
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i <;> by_cases hkj : k = j
    · subst hki; subst hkj; exact absurd rfl h
    · subst hki; simp [h]
    · simp [hki]
    · simp [hki]

end WaveEquation3D

namespace WaveEquation3D

/--
[angularMetric_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma angularMetric_nonneg
  {n : ℕ}
  {nf : NullFrame n}
  {X : Fin (n + 1) → ℝ} :
-- imply
  0 ≤ angularMetric n nf X X := by
-- proof
  simp only [angularMetric]
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

end WaveEquation3D

namespace WaveEquation3D

/--
[angularMetric_pos_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma angularMetric_pos_def
  {n : ℕ}
  {nf : NullFrame n}
  {X : Fin (n + 1) → ℝ}
-- given
  (hL : minkowskiInner n nf.L X = 0)
  (hLb : minkowskiInner n nf.Lb X = 0)
  (hX : X ≠ 0) :
-- imply
  0 < angularMetric n nf X X := by
-- proof
  simp only [angularMetric]
  apply Finset.sum_pos'
  · intro i _; exact mul_self_nonneg _
  · by_contra h_none
    push Not at h_none
    apply hX
    have h_zero : ∀ i : Fin (n - 1), minkowskiInner n (nf.e i) X = 0 := by
      intro i
      have h1 := h_none i (Finset.mem_univ i)
      have h2 := mul_self_nonneg (minkowskiInner n (nf.e i) X)
      exact mul_self_eq_zero.mp (le_antisymm h1 h2)
    have := nf.completeness X
    rw [hLb, hL] at this
    simp only [mul_zero, zero_smul, zero_add] at this
    rw [this]
    simp only [h_zero, zero_smul, Finset.sum_const_zero]

end WaveEquation3D

namespace WaveEquation3D

/--
[minkowskiMetric_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma minkowskiMetric_sq
  {n : ℕ} :
-- imply
  minkowskiMetric n * minkowskiMetric n = 1 := by
-- proof
  ext i j
  simp only [minkowskiMetric, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hij : i = j
  · subst hij; by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  · by_cases hj : (j : ℕ) = 0 <;> simp [hij, hj]

end WaveEquation3D

namespace WaveEquation3D

/--
[minkowskiMetric_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma minkowskiMetric_inv
  {n : ℕ} :
-- imply
  (minkowskiMetric n)⁻¹ = minkowskiMetric n :=
-- proof
  inv_eq_left_inv (minkowskiMetric_sq n)

end WaveEquation3D

namespace WaveEquation3D

/--
[minkowskiInner_eta_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma minkowskiInner_eta_cancel
  {n : ℕ}
  {V W : Fin (n + 1) → ℝ} :
-- imply
  minkowskiInner n V (minkowskiMetric n *ᵥ W) = dotProduct V W := by
-- proof
  simp only [minkowskiInner, mulVec_mulVec, minkowskiMetric_sq, one_mulVec]

end WaveEquation3D

namespace WaveEquation3D

/--
[nullFrame_inverse_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean)
-/
@[path]
lemma nullFrame_inverse_decomposition
  {n : ℕ}
  {nf : NullFrame n}
  {μ ν : Fin (n + 1)} :
-- imply
  (minkowskiMetric n)⁻¹ μ ν = -(1 / 2) * nf.L μ * nf.Lb ν - (1 / 2) * nf.Lb μ * nf.L ν + ∑ i : Fin (n - 1), nf.e i μ * nf.e i ν := by
-- proof
  rw [minkowskiMetric_inv]
  have h_entry : minkowskiMetric n μ ν = (minkowskiMetric n *ᵥ Pi.single ν 1) μ := by
    simp [mulVec, dotProduct, minkowskiMetric, Matrix.of_apply, Pi.single_apply]
  rw [h_entry]
  have h_comp := nf.completeness (minkowskiMetric n *ᵥ Pi.single ν 1)
  have h_μ := congr_fun h_comp μ
  rw [h_μ]
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    minkowskiInner_eta_cancel,
    dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  · ring
  · congr 1; ext i; ring

end WaveEquation3D


-- created on 2026-10-23
