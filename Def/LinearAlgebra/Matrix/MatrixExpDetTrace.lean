/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MatrixExpDetTrace.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
open scoped BigOperators

/-!
# Determinant and finite-series formulas for the matrix exponential

This file proves that the determinant of a complex matrix exponential is the exponential of its
trace, and that the exponential series truncates for a nilpotent matrix.
-/


namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
noncomputable def matrixExp_eigenbasis {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) :
    Module.Basis (Σ z, Module.Basis.ofVectorSpaceIndex ℂ (f.eigenspace z)) ℂ V := by
  classical
  let b (z : ℂ) := Module.Basis.ofVectorSpace ℂ (f.eigenspace z)
  exact (DFinsupp.basis b).map (f.eigenspaces_iSupIndep.linearEquiv h)

omit [Fintype n] [DecidableEq n] in
noncomputable def matrixExp_diagonalizingBasis
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] (b₀ : Module.Basis ι ℂ V)
    (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) : Module.Basis ι ℂ V :=
  (matrixExp_eigenbasis f h).reindex (b₀.indexEquiv (matrixExp_eigenbasis f h)).symm

omit [Fintype n] [DecidableEq n] in
noncomputable def matrixExp_diagonalizingEigenvalue
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] (b₀ : Module.Basis ι ℂ V)
  (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) (i : ι) : ℂ :=
  (b₀.indexEquiv (matrixExp_eigenbasis f h) i).1

noncomputable def matrixExp_changeBasisAlgEquiv
    (b : Module.Basis n ℂ (n → ℂ)) : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ :=
  (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)).trans
    (LinearMap.toMatrixAlgEquiv b)

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted
