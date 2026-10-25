/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Topology.Connected.Basic


noncomputable section

open Matrix Finset BigOperators

structure HypersurfacePatch (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  smooth : ContDiffOn ℝ ⊤ f domain
  immersion : ∀ x ∈ domain, Function.Injective (fderiv ℝ f x)

end
