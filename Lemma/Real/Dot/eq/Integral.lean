import sympy.integrals.integrals
import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
open MeasureTheory Matrix


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {f : ℝ → Fin n → ℝ}
-- given
  (hf : Integrable f volume) :
-- imply
  A *ᵥ (∫ x : ℝ, f x) = ∫ x : ℝ, A *ᵥ f x := by
-- proof
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  show L (∫ x : ℝ, f x) = ∫ x : ℝ, L (f x)
  rw [L.integral_comp_comm hf]


-- created on 2026-09-26
