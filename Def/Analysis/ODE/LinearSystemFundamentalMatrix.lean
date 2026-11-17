/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.ProjIcc
public import Structure.Analysis.ODE.MaximalSolution

@[expose] public section

open MeasureTheory

/-!
# Fundamental matrices for linear ODE systems

This file proves global existence and uniqueness for continuous linear systems, constructs their
principal matrix solutions, and proves Liouville's determinant formula.
-/


namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

noncomputable def fundMatrix_matrixMulCLM {n : ℕ} :
    (Fin n → Fin n → ℝ) →L[ℝ]
      (Fin n → Fin n → ℝ) →L[ℝ] Fin n → Fin n → ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      ((Fin n → Fin n → ℝ) →ₗ[ℝ] Fin n → Fin n → ℝ) ≃ₗ[ℝ]
        (Fin n → Fin n → ℝ) →L[ℝ] Fin n → Fin n → ℝ).toLinearMap.comp
      (mulLinearMap ℝ))

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted
