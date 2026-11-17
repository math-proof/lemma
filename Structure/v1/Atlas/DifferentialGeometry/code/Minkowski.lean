/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Minkowski.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Def.v1.Atlas.DifferentialGeometry.code.Minkowski


public noncomputable section

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
