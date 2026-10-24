/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Hoffman_Wielandt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Background_Weyl
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Background_Weyl

open Matrix Real Finset

noncomputable section

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

/-- **Hoffman-Wielandt inequality.** For matrices `A`, `B : Fin d × Fin T → ℝ` with
ordered singular value decompositions `S_A` and `S_B` of the same rank, the sum of squared
differences of corresponding singular values is bounded by the squared Frobenius norm of
`A - B`:  $\sum_k (\sigma_k(A) - \sigma_k(B))^2 \le \|A - B\|_F^2$. -/
end
