/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/LinearSystemFundamentalMatrix.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.ProjIcc
import Structure.Analysis.ODE.MaximalSolution
import Lemma.Set.Any_And_EqOnAndAll_HasDerivAt.of.EqOn_Inter.All_HasDerivAt.All_HasDerivAt.IsOpen.IsOpen
import Theorem.Analysis.ODE.LinearSystemFundamentalMatrix.Part2
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
