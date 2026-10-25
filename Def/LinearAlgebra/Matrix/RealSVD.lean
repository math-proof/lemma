/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RealSVD.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Basis
/-!
# Rectangular real singular value decomposition

This file proves that every rectangular real matrix admits a singular value decomposition with
orthogonal left and right factors and a rectangular diagonal matrix of nonnegative singular values.
-/


namespace Matrix

noncomputable def realSVD_normalizedImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : Module.finrank ℝ E = n) {m : ℕ} (i : Fin m) : F :=
  if hi : i.val < n then
    (T.singularValues i.val)⁻¹ •
      T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) ⟨i.val, hi⟩)
  else 0

def realSVD_nonzeroImageIndices
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) (n m : ℕ) : Set (Fin m) :=
  {i | i.val < n ∧ T.singularValues i.val ≠ 0}

end Matrix
