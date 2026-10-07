import Mathlib
import sympy.Basic

open MeasureTheory

/--
[MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod.lean)
-/
@[main]
private lemma main
  {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [SFinite μ]
  {ν : Measure Y} [SFinite ν]
  {ρ : Measure Z} [SFinite ρ]
  {f : X × Y × Z → E}
-- given
  (hf : Integrable f (μ.prod (ν.prod ρ))) :
-- imply
  ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ z, ∫ y, ∫ x, f (x, y, z) ∂μ ∂ν ∂ρ := by
-- proof
  have h1 : ∀ᵐ x ∂μ, Integrable (fun p : Y × Z => f (x, p)) (ν.prod ρ) := hf.prod_right_ae
  have e1 : ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ x, ∫ p, f (x, p) ∂(ν.prod ρ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h1] with x hx
    exact (integral_prod _ hx).symm
  have hf' : Integrable (Function.uncurry fun (x : X) (p : Y × Z) => f (x, p)) (μ.prod (ν.prod ρ)) := hf
  have e2 : ∫ x, ∫ p, f (x, p) ∂(ν.prod ρ) ∂μ = ∫ p, ∫ x, f (x, p) ∂μ ∂(ν.prod ρ) :=
    integral_integral_swap hf'
  have hG : Integrable (fun p : Y × Z => ∫ x, f (x, p) ∂μ) (ν.prod ρ) := hf.integral_prod_right
  rw [e1, e2]
  exact integral_prod_symm _ hG


-- created on 2026-10-05
