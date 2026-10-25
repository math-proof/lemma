/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectForceCutClosed (R : FKRectTorus)
    (omega : R.Configuration) : R.Configuration :=
  fun a => if a ∈ fkRectTorusCutEdges R then false else omega a

end
end StatMech.FrontierD
