module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.Analysis.Complex.Wiman.CoefficientExponentialFamily
public import Theorem.Complex.Wiman.RadialMajorant

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Complex


/--
[wimanCoefficientMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem wimanCoefficientMeasure_singleton
  {f : ℂ → ℂ}
  {n : ℕ} :
-- imply
  wimanCoefficientMeasure f {n} = ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ :=
-- proof
  (Measure.sum_smul_dirac_singleton)

/--
[integrable_exp_mul_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem integrable_exp_mul_wimanCoefficientMeasure
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  Integrable (fun n : ℕ => Real.exp (x * (n : ℝ))) (wimanCoefficientMeasure f) := by
-- proof
  rw [wimanCoefficientMeasure]
  refine integrable_sum_dirac (fun n => by simp) ?_
  refine (summable_wimanTerm (f := f) (r := Real.exp x) hf).congr fun n => ?_
  rw [wimanTerm, ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_comm x (n : ℝ), Real.exp_nat_mul,
    abs_of_nonneg (pow_nonneg (Real.exp_pos x).le n)]

/--
[integrableExpSet_wimanCoefficientMeasure_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem integrableExpSet_wimanCoefficientMeasure_eq_univ
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  integrableExpSet (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) = Set.univ := by
-- proof
  ext x
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_exp_mul_wimanCoefficientMeasure (f := f) (x := x) hf

/--
[mem_interior_integrableExpSet_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem mem_interior_integrableExpSet_wimanCoefficientMeasure
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  x ∈ interior (integrableExpSet (fun n : ℕ => (n : ℝ))
    (wimanCoefficientMeasure f)) := by
-- proof
  simp [integrableExpSet_wimanCoefficientMeasure_eq_univ (f := f) hf]

/--
[integral_exp_mul_wimanCoefficientMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem integral_exp_mul_wimanCoefficientMeasure
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ∫ n : ℕ, Real.exp (x * (n : ℝ)) ∂(wimanCoefficientMeasure f) =
    wimanMajorant f (Real.exp x) := by
-- proof
  have hInt := integrable_exp_mul_wimanCoefficientMeasure (f := f) (x := x) hf
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

/--
[wiman_mgf_eq_majorant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem wiman_mgf_eq_majorant
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  mgf (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) x =
    wimanMajorant f (Real.exp x) := by
-- proof
  rw [mgf, integral_exp_mul_wimanCoefficientMeasure (f := f) (x := x) hf]

/--
[wiman_cgf_eq_growth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem wiman_cgf_eq_growth
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
    (wimanCoefficientMeasure f) x = wimanGrowth f x := by
-- proof
  rw [cgf, wimanGrowth, wiman_mgf_eq_majorant (f := f) (x := x) hf]

/--
[wimanCoefficientMeasure_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem wimanCoefficientMeasure_ne_zero
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
  rw [← wimanCoefficientMeasure_singleton (f := f) (n := n), hzero]
  simp

/--
[isProbabilityMeasure_wimanTiltedMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem isProbabilityMeasure_wimanTiltedMeasure
  {f : ℂ → ℂ}
  {x : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
-- imply
  IsProbabilityMeasure (wimanTiltedMeasure f x) := by
-- proof
  let _ : NeZero (wimanCoefficientMeasure f) :=
    ⟨wimanCoefficientMeasure_ne_zero (f := f) hne⟩
  exact isProbabilityMeasure_tilted (integrable_exp_mul_wimanCoefficientMeasure (f := f) (x := x) hf)

/--
[wimanTiltedMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem wimanTiltedMeasure_singleton
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
    lintegral_singleton, wiman_mgf_eq_majorant (f := f) (x := x) hf,
    wimanCoefficientMeasure_singleton]
  have hratio :
    0 ≤ Real.exp (x * (n : ℝ)) / wimanMajorant f (Real.exp x) :=
    div_nonneg (Real.exp_pos _).le (wimanMajorant_nonneg (f := f) (r := Real.exp x))
  rw [← ENNReal.ofReal_mul hratio]
  congr 1
  rw [wimanTerm, abs_of_pos (Real.exp_pos x), mul_comm x (n : ℝ), Real.exp_nat_mul]
  ring

/--
[wimanTiltedMeasure_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean)
-/
@[path]
theorem wimanTiltedMeasure_eq_sum
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
  rw [wimanTiltedMeasure_singleton (f := f) (x := x) (n := n) hf,
    Measure.sum_smul_dirac_singleton]


-- created on 2026-10-20
-- updated on 2026-11-23
