/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

def centralCylinderSite (n : Nat)
    (q : CubicalCell (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) : Site 3 := fun i =>
  if i = (0 : Fin 3) then q.x.val
  else if i = (1 : Fin 3) then q.y.val
  else (centralSquareSide n : Int) - q.z.val


end
end StatMech.FrontierA
