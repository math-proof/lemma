/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false

open ContinuousAlternatingMap


namespace DolbeaultHodgeMathlib

/-- The space $\Omega^k(\mathbb{R}^n)$ of (continuous) differential $k$-forms on Euclidean
$n$-space, modelled as maps from points to continuous alternating $k$-linear forms. -/
def DiffForm (n k : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ

end DolbeaultHodgeMathlib
