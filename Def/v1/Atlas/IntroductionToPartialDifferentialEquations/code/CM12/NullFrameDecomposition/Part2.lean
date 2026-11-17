/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/NullFrameDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Real.Basic
public import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM12.NullFrameDecomposition

@[expose] public section

set_option maxHeartbeats 800000


noncomputable section

open Matrix

namespace NullFrame

/-- The angular (transverse) part $h(X, Y) = \sum_i m(e_{(i)}, X) \, m(e_{(i)}, Y)$ of
the Minkowski metric appearing in the null frame decomposition. -/
def angularMetric (n : ℕ) (nf : NullFrameData n) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n - 1), minkowskiInner n (nf.e i) X * minkowskiInner n (nf.e i) Y

end NullFrame
end
