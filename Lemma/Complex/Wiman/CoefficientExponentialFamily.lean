import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.CoefficientExponentialFamily
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Complex


namespace Complex

/--
[wimanCoefficientMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma wimanCoefficientMeasure_singleton
  {f : ℂ → ℂ}
  {n : ℕ} :
-- imply
  wimanCoefficientMeasure f {n} = ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ :=
-- proof
Measure.sum_smul_dirac_singleton

end Complex

namespace Complex

/--
[integrable_exp_mul_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma integrable_exp_mul_wimanCoefficientMeasure
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  Integrable (fun n : ℕ => Real.exp (x * (n : ℝ))) (wimanCoefficientMeasure f) := by
-- proof
  rw [wimanCoefficientMeasure]
  refine integrable_sum_dirac (fun n => by simp) ?_
  refine (summable_wimanTerm f hf (Real.exp x)).congr fun n => ?_
  rw [wimanTerm, ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_comm x (n : ℝ), Real.exp_nat_mul,
    abs_of_nonneg (pow_nonneg (Real.exp_pos x).le n)]

end Complex

namespace Complex

/--
[integrableExpSet_wimanCoefficientMeasure_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma integrableExpSet_wimanCoefficientMeasure_eq_univ
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  integrableExpSet (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) = Set.univ := by
-- proof
  ext x
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_exp_mul_wimanCoefficientMeasure f hf x

end Complex

namespace Complex

/--
[mem_interior_integrableExpSet_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma mem_interior_integrableExpSet_wimanCoefficientMeasure
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  x ∈ interior (integrableExpSet (fun n : ℕ => (n : ℝ))
    (wimanCoefficientMeasure f)) := by
-- proof
  simp [integrableExpSet_wimanCoefficientMeasure_eq_univ f hf]

end Complex

namespace Complex

/--
[integral_exp_mul_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma integral_exp_mul_wimanCoefficientMeasure
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ∫ n : ℕ, Real.exp (x * (n : ℝ)) ∂(wimanCoefficientMeasure f) =
    wimanMajorant f (Real.exp x) := by
-- proof
  have hInt := integrable_exp_mul_wimanCoefficientMeasure f hf x
  rw [wimanCoefficientMeasure] at hInt
  have hsum : Summable (fun n : ℕ =>
    (ENNReal.ofReal ‖wimanTaylorCoefficient f n‖).toReal *
      ‖Real.exp (x * (n : ℝ))‖) :=
    hInt.summable_of_dirac
  rw [wimanCoefficientMeasure,
    integral_sum_dirac_eq_tsum
      (f := fun n : ℕ => Real.exp (x * (n : ℝ))) (fun n => by simp) hsum,
    wimanMajorant]
  apply tsum_congr
  intro n
  rw [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul, wimanTerm,
    abs_of_pos (Real.exp_pos x), mul_comm x (n : ℝ), Real.exp_nat_mul]

end Complex

namespace Complex

/--
[wiman_mgf_eq_majorant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma wiman_mgf_eq_majorant
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  mgf (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) x =
    wimanMajorant f (Real.exp x) := by
-- proof
  rw [mgf, integral_exp_mul_wimanCoefficientMeasure f hf x]

end Complex

namespace Complex

/--
[wiman_cgf_eq_growth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma wiman_cgf_eq_growth
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
    (wimanCoefficientMeasure f) x = wimanGrowth f x := by
-- proof
  rw [cgf, wimanGrowth, wiman_mgf_eq_majorant f hf x]

end Complex

namespace Complex

/--
[wimanCoefficientMeasure_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma wimanCoefficientMeasure_ne_zero
  {f : ℂ → ℂ}
-- given
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  wimanCoefficientMeasure f ≠ 0 := by
-- proof
  obtain ⟨n, hn⟩ := hne
  have hmass : ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hn))
  intro hzero
  apply hmass
  rw [← wimanCoefficientMeasure_singleton f n, hzero]
  simp

end Complex

namespace Complex

/--
[isProbabilityMeasure_wimanTiltedMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma isProbabilityMeasure_wimanTiltedMeasure
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  IsProbabilityMeasure (wimanTiltedMeasure f x) := by
-- proof
  let _ : NeZero (wimanCoefficientMeasure f) :=
    ⟨wimanCoefficientMeasure_ne_zero f hne⟩
  exact isProbabilityMeasure_tilted (integrable_exp_mul_wimanCoefficientMeasure f hf x)

end Complex

namespace Complex

/--
[wimanTiltedMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma wimanTiltedMeasure_singleton
  {f : ℂ → ℂ}
  {x : ℝ}
  {n : ℕ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanTiltedMeasure f x {n} =
    ENNReal.ofReal
    (wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x)) := by
-- proof
  rw [wimanTiltedMeasure,
    ProbabilityTheory.tilted_mul_apply_mgf'
      (μ := wimanCoefficientMeasure f) (X := fun n : ℕ => (n : ℝ))
      (t := x) (measurableSet_singleton n),
    lintegral_singleton, wiman_mgf_eq_majorant f hf x,
    wimanCoefficientMeasure_singleton]
  have hratio :
    0 ≤ Real.exp (x * (n : ℝ)) / wimanMajorant f (Real.exp x) :=
    div_nonneg (Real.exp_pos _).le (wimanMajorant_nonneg f (Real.exp x))
  rw [← ENNReal.ofReal_mul hratio]
  congr 1
  rw [wimanTerm, abs_of_pos (Real.exp_pos x), mul_comm x (n : ℝ), Real.exp_nat_mul]
  ring

end Complex

namespace Complex

/--
[wimanTiltedMeasure_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
lemma wimanTiltedMeasure_eq_sum
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanTiltedMeasure f x =
    Measure.sum fun n : ℕ =>
    ENNReal.ofReal
    (wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x)) •
    Measure.dirac n := by
-- proof
  apply Measure.ext_iff_singleton.mpr
  intro n
  rw [wimanTiltedMeasure_singleton f hf x n,
    Measure.sum_smul_dirac_singleton]
end



-- created on 2026-10-20
-- updated on 2026-10-23
