/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean -/

import sympy.atlas.Analysis.Complex.Wiman.RadialMajorant
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Moments.Tilted

namespace Complex

open MeasureTheory ProbabilityTheory

open scoped ENNReal

noncomputable section

/-- The logarithm of the radial Taylor majorant at logarithmic radius `x`. -/
def wimanGrowth (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  Real.log (wimanMajorant f (Real.exp x))

/-- The atomic measure whose mass at `n` is the norm of the `n`th Taylor coefficient. -/
def wimanCoefficientMeasure (f : ℂ → ℂ) : Measure ℕ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ • Measure.dirac n

/-- The coefficient measure tilted at logarithmic radius `x`. -/
def wimanTiltedMeasure (f : ℂ → ℂ) (x : ℝ) : Measure ℕ :=
  (wimanCoefficientMeasure f).tilted fun n : ℕ => x * (n : ℝ)

/-- The mass of a singleton under the coefficient measure is its coefficient norm. -/
@[simp]
theorem wimanCoefficientMeasure_singleton (f : ℂ → ℂ) (n : ℕ) :
    wimanCoefficientMeasure f {n} = ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ := by
  exact Measure.sum_smul_dirac_singleton

/-- Every exponential moment of the coefficient measure is integrable for an entire function. -/
theorem integrable_exp_mul_wimanCoefficientMeasure
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    Integrable (fun n : ℕ => Real.exp (x * (n : ℝ))) (wimanCoefficientMeasure f) := by
  rw [wimanCoefficientMeasure]
  refine integrable_sum_dirac (fun n => by simp) ?_
  refine (summable_wimanTerm f hf (Real.exp x)).congr fun n => ?_
  rw [wimanTerm, ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_comm x (n : ℝ), Real.exp_nat_mul,
    abs_of_nonneg (pow_nonneg (Real.exp_pos x).le n)]

/-- The exponential-integrability interval of the coefficient measure is all of `ℝ`. -/
theorem integrableExpSet_wimanCoefficientMeasure_eq_univ
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    integrableExpSet (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) = Set.univ := by
  ext x
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_exp_mul_wimanCoefficientMeasure f hf x

/-- Every real parameter lies in the interior exponential-integrability interval. -/
theorem mem_interior_integrableExpSet_wimanCoefficientMeasure
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    x ∈ interior (integrableExpSet (fun n : ℕ => (n : ℝ))
      (wimanCoefficientMeasure f)) := by
  simp [integrableExpSet_wimanCoefficientMeasure_eq_univ f hf]

/-- The exponential moment integral is the radial Taylor majorant. -/
theorem integral_exp_mul_wimanCoefficientMeasure
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    ∫ n : ℕ, Real.exp (x * (n : ℝ)) ∂(wimanCoefficientMeasure f) =
      wimanMajorant f (Real.exp x) := by
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

/-- The MGF of the coefficient measure is the radial Taylor majorant. -/
theorem wiman_mgf_eq_majorant
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    mgf (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) x =
      wimanMajorant f (Real.exp x) := by
  rw [mgf, integral_exp_mul_wimanCoefficientMeasure f hf x]

/-- The coefficient-measure cumulant-generating function is the logarithmic majorant. -/
theorem wiman_cgf_eq_growth
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
        (wimanCoefficientMeasure f) x = wimanGrowth f x := by
  rw [cgf, wimanGrowth, wiman_mgf_eq_majorant f hf x]

/-- A nonzero Taylor coefficient gives nonzero mass to the coefficient measure. -/
theorem wimanCoefficientMeasure_ne_zero
    (f : ℂ → ℂ) (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
    wimanCoefficientMeasure f ≠ 0 := by
  obtain ⟨n, hn⟩ := hne
  have hmass : ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hn))
  intro hzero
  apply hmass
  rw [← wimanCoefficientMeasure_singleton f n, hzero]
  simp

/-- With nonzero coefficient mass, the tilted coefficient measure is a probability measure. -/
theorem isProbabilityMeasure_wimanTiltedMeasure
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) (x : ℝ) :
    IsProbabilityMeasure (wimanTiltedMeasure f x) := by
  let _ : NeZero (wimanCoefficientMeasure f) :=
    ⟨wimanCoefficientMeasure_ne_zero f hne⟩
  exact isProbabilityMeasure_tilted (integrable_exp_mul_wimanCoefficientMeasure f hf x)

/-- The tilted singleton masses are the Taylor terms normalized by the majorant. -/
@[simp]
theorem wimanTiltedMeasure_singleton
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) (n : ℕ) :
    wimanTiltedMeasure f x {n} =
      ENNReal.ofReal
        (wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x)) := by
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

/-- The tilted measure has the atomic mass representation of normalized Taylor terms. -/
theorem wimanTiltedMeasure_eq_sum
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    wimanTiltedMeasure f x =
      Measure.sum fun n : ℕ =>
        ENNReal.ofReal
          (wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x)) •
            Measure.dirac n := by
  apply Measure.ext_iff_singleton.mpr
  intro n
  rw [wimanTiltedMeasure_singleton f hf x n,
    Measure.sum_smul_dirac_singleton]

end
