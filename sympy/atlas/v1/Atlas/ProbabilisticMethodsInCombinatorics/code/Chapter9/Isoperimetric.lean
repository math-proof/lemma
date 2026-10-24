/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Isoperimetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
set_option maxHeartbeats 800000

namespace IsoperimetricEuclidean

open MeasureTheory Metric Set
/-- **Euclidean isoperimetric inequality** (Theorem 9.4.1). Among all measurable subsets of
$\mathbb{R}^n$ with a fixed Lebesgue volume, the closed ball minimizes the volume of the
$t$-thickening: if $\operatorname{vol}(A) = \operatorname{vol}(B(c, r))$, then for every
$t \ge 0$, $\operatorname{vol}(B(c, r)_t) \le \operatorname{vol}(A_t)$. -/
end IsoperimetricEuclidean
