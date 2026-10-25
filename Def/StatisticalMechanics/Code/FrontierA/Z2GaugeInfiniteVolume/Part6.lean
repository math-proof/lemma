/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part6
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalPaddedDisorderFreeEnergy (beta : Real) (a b : Nat)
    (lx rx ly ry lz rz : Nat) : Real :=
  multibondDisorderFreeEnergy cubicalDualEnds
    (fun _ : CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz) =>
      gaugeDualCoupling beta)
    (cubicalPaddedXYSheet a b lx rx ly ry lz rz)


end
end StatMech.FrontierA
