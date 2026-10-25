/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.SpaceFillingCurve
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.SpaceFillingCurve
set_option maxHeartbeats 800000

open scoped Classical


namespace EuclideanTSP

/-- The two-dimensional Euclidean plane $\mathbb{R}^2$, the ambient space for the
Euclidean travelling salesman problem. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

end EuclideanTSP
