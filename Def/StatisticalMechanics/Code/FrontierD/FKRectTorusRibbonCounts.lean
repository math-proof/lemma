/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonCounts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.GenusOneRibbonEulerDefect
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonCounts


namespace StatMech.FrontierD

def fkRectTorusCellularFaceCount (R : FKRectTorus) : Nat :=
  R.width * R.height


end StatMech.FrontierD
