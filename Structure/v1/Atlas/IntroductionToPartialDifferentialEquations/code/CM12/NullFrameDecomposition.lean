/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM12.NullFrameDecomposition
set_option maxHeartbeats 800000


noncomputable section

open Matrix

namespace NullFrame

/-- A null frame for $\mathbb{R}^{1+n}$ (Definition 2.2.1): a basis
$\{L, \underline{L}, e_{(1)}, \ldots, e_{(n-1)}\}$ where $L$ and $\underline{L}$ are null
vectors normalized by $m(L, \underline{L}) = -2$, and the $e_{(i)}$ are
$m$-orthonormal vectors that span the $m$-orthogonal complement of
$\operatorname{span}(L, \underline{L})$. The `completeness` field expresses every vector
$X$ in null-frame components. -/
structure NullFrameData (n : ℕ) where
  L : Fin (n + 1) → ℝ
  Lb : Fin (n + 1) → ℝ
  e : Fin (n - 1) → (Fin (n + 1) → ℝ)
  L_null : minkowskiInner n L L = 0
  Lb_null : minkowskiInner n Lb Lb = 0
  L_Lb_inner : minkowskiInner n L Lb = -2
  e_orthonormal : ∀ i j : Fin (n - 1),
    minkowskiInner n (e i) (e j) = if i = j then 1 else 0
  L_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n L (e i) = 0
  Lb_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n Lb (e i) = 0
  completeness : ∀ X : Fin (n + 1) → ℝ,
    X = (-(1/2) * minkowskiInner n Lb X) • L
      + (-(1/2) * minkowskiInner n L X) • Lb
      + ∑ i, (minkowskiInner n (e i) X) • (e i)

end NullFrame
end
