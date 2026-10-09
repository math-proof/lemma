import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.Module.FiniteDimension
import sympy.Basic
open MeasureTheory


/--
On a finite-dimensional parameter space, the parametric derivative `y ↦ fderiv ℝ (fun θ ↦ F θ y) θ₀` of a family of
measurable functions `F θ` that are differentiable in `θ` at `θ₀` is strongly measurable
(each coordinate is a pointwise limit of measurable difference quotients).
-/
@[path]
private lemma main
  [MeasurableSpace S] [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  {F : Θ → S → ℝ}
  {θ₀ : Θ}
-- given
  (h₀ : ∀ θ, Measurable (F θ))
  (h₁ : ∀ y, DifferentiableAt ℝ (fun θ => F θ y) θ₀) :
-- imply
  StronglyMeasurable (fun y => fderiv ℝ (fun θ => F θ y) θ₀) := by
-- proof
  classical
  let b := Module.finBasis ℝ Θ
  have hc : ∀ i, Measurable (fun y => fderiv ℝ (fun θ => F θ y) θ₀ (b i)) := fun i =>
    measurable_of_tendsto_metrizable
      (f := fun (n : ℕ) y => (n : ℝ) • (F (θ₀ + (n : ℝ)⁻¹ • b i) y - F θ₀ y))
      (fun n => by
        have h₂ := h₀ (θ₀ + (n : ℝ)⁻¹ • b i)
        have h₃ := h₀ θ₀
        fun_prop)
      (tendsto_pi_nhds.2 fun y => ((h₁ y).hasFDerivAt.lim_real (b i)).comp tendsto_natCast_atTop_atTop)
  have e : (fun y => fderiv ℝ (fun θ => F θ y) θ₀) =
      fun y => ∑ i, fderiv ℝ (fun θ => F θ y) θ₀ (b i) • LinearMap.toContinuousLinearMap (b.coord i) := by
    funext y
    ext v
    simp only [_root_.sum_apply, _root_.smul_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [e]
  apply Finset.stronglyMeasurable_fun_sum _ fun i _ => (hc i).stronglyMeasurable.smul_const _


-- created on 2026-10-07
