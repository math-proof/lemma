/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Minkowski.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Def.v1.Atlas.DifferentialGeometry.code.Minkowski


noncomputable section

open Finset

namespace Minkowski

variable {n : ℕ}

structure SpacelikeHypersurface (n : ℕ) where
  U : Set (Fin n → ℝ)
  hU : IsOpen U
  f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  smooth : ContDiffOn ℝ ⊤ f U
  linearIndep : ∀ x ∈ U, LinearIndependent ℝ (partials f x)
  spacelike : ∀ x ∈ U, IsPositiveDefiniteOn
    (Submodule.span ℝ (Set.range (partials f x)))

end Minkowski
end
