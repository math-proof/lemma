/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
set_option maxHeartbeats 800000


noncomputable section

open Matrix

namespace NullFrame

/-- The Minkowski metric on $\mathbb{R}^{1+n}$ as a matrix:
$m_{\mu \nu} = \operatorname{diag}(-1, 1, 1, \ldots, 1)$. -/
def minkowskiMetric (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if i = j then (if (i : ℕ) = 0 then -1 else 1) else 0

/-- The Minkowski inner product of two vectors $X, Y \in \mathbb{R}^{1+n}$:
$m(X, Y) = m_{\alpha \beta} X^{\alpha} Y^{\beta}$. -/
def minkowskiInner (n : ℕ) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  dotProduct X (minkowskiMetric n *ᵥ Y)

end NullFrame
end
