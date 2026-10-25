/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part4
open Finset


namespace StatMech.FrontierD

noncomputable def sixVertexTorusArrowPartitionSum (T : EvenTorus) (c : ℝ) : ℝ :=
  ∑ ω : SixVertexArrows T, ω.weight c


end StatMech.FrontierD
