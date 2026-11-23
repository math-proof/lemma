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
public import Theorem.Set.Any_And_EqOnAndAll_HasDerivAt.of.EqOn_Inter.All_HasDerivAt.All_HasDerivAt.IsOpen.IsOpen
public import Theorem.Analysis.ODE.LinearSystemFundamentalMatrix.Part2

@[expose] public section

open MeasureTheory

/-!
# Fundamental matrices for linear ODE systems

This file proves global existence and uniqueness for continuous linear systems, constructs their
principal matrix solutions, and proves Liouville's determinant formula.
-/


namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

noncomputable def fundMatrix_detDifferential {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, M (σ j) j) * N (σ i) i

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted
