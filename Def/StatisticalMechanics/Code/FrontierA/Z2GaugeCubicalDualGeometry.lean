/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter.Part2
import Structure.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

def cubicalCellFaces {a b c : Nat} (q : CubicalCell a b c) :
    Finset (CubicalPlaquette a b c) :=
  {.xy q.x q.y q.z.castSucc, .xy q.x q.y q.z.succ,
    .xz q.x q.y.castSucc q.z, .xz q.x q.y.succ q.z,
    .yz q.x.castSucc q.y q.z, .yz q.x.succ q.y q.z}


end
end StatMech.FrontierA
