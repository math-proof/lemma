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
import Structure.v1.Atlas.DifferentialGeometry.code.Minkowski


noncomputable section

open Finset

namespace Minkowski

variable {n : ℕ}

def orientationMatrix (f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)) (x : Fin n → ℝ)
    (ν : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (i : Fin (n + 1)) (j : Fin (n + 1)) =>
    Fin.lastCases (ν i) (fun k => partials f x k i) j

end Minkowski
end
