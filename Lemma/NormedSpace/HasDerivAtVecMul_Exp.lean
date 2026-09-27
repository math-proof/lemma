import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import sympy.stats.generator_matrix
import sympy.Basic
open Matrix NormedSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
-- given
  (Q : Matrix S S ℝ)
  (ξ : S → ℝ)
  (t : ℝ) :
-- imply
  HasDerivAt (fun s : ℝ => ξ ᵥ* exp (s • Q)) (ξ ᵥ* exp (t • Q) ᵥ* Q) t := by
-- proof
  let _ : NormedRing (Matrix S S ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix S S ℝ) := Matrix.linftyOpNormedAlgebra
  let L : Matrix S S ℝ →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun M => ξ ᵥ* M
      map_add' := fun M N => by simp [Matrix.vecMul_add]
      map_smul' := fun a M => by simp [Matrix.vecMul_smul] }
  convert (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) Q t) using 1 <;> try rfl
  rw [Matrix.vecMul_vecMul]
  rfl


-- created on 2026-09-26
