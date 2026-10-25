/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalPaddedWilsonExpectation (beta : Real) (a b : Nat)
    (lx rx ly ry lz rz : Nat) : Real :=
  gaugeWilsonExpectation
    (cubicalPlaquetteIncidence
      (a := lx + a + rx) (b := ly + b + ry) (c := lz + rz))
    (fun _ : CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz) => beta)
    ((cubicalXYLoop (a := a) (b := b) (c := 0) (0 : Fin 1)).map
      (cubicalEdgeChart lx ly lz
        (by omega) (by omega) (by omega)))


end
end StatMech.FrontierA
