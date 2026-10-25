/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/SphereCuttingBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option maxHeartbeats 400000

open Set


namespace SphereArrangement

/-- Three-dimensional Euclidean space $\mathbb{R}^3$ used for the sphere-cutting bound. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

end SphereArrangement
