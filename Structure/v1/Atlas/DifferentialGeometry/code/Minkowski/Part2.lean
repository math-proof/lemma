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
import Def.v1.Atlas.DifferentialGeometry.code.Minkowski.Part2


noncomputable section

open Finset

namespace Minkowski

variable {n : ℕ}

structure IsGaussNormal {n : ℕ} (S : SpacelikeHypersurface n) (x : Fin n → ℝ)
    (ν : Fin (n + 1) → ℝ) : Prop where
  timelike : minkowskiInner n ν ν = -1
  orthogonal : ∀ i : Fin n, minkowskiInner n ν (partials S.f x i) = 0
  positive_orientation : (orientationMatrix S.f x ν).det > 0

end Minkowski
end
