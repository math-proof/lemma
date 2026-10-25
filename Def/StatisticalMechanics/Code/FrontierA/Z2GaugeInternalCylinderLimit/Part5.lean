/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part4
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

def cubicalInternalCentralWilsonExpectation
    (K : Real) (n m : Nat) (hnm : centralSquareSide n <= m) : Real :=
  gaugeWilsonExpectation cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
      (oddCubeSide m) => K)
    (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalInternalCentralSheet (centralSquareSide n) m hnm))


end
end StatMech.FrontierA
