/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part7
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def cubicalDualL1 {a b c : Nat} :
    CubicalDualVertex a b c -> CubicalDualVertex a b c -> Nat
  | some q, some q' =>
      Nat.dist q.x.val q'.x.val + Nat.dist q.y.val q'.y.val +
        Nat.dist q.z.val q'.z.val
  | _, _ => 0

end
end StatMech.FrontierA
