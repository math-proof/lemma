/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part4
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalPaddedXYSheet (a b lx rx ly ry lz rz : Nat) :
    Finset (CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz)) :=
  (cubicalXYSheet (a := a) (b := b) (c := 0) (0 : Fin 1)).map
    (cubicalPlaquetteChart lx ly lz (by omega) (by omega) (by omega))

end
end StatMech.FrontierA
