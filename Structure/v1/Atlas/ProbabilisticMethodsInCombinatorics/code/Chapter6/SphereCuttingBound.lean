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
import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.SphereCuttingBound
set_option maxHeartbeats 400000

open Set


namespace SphereArrangement

/-- A sphere in $\mathbb{R}^3$ specified by a center and a strictly positive radius. -/
structure Sphere3 where
  center : R3
  radius : ℝ
  radius_pos : 0 < radius

end SphereArrangement
