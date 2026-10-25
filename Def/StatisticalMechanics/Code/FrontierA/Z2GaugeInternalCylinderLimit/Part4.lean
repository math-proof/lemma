/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part3
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

def centralCylinderVertexSite (n : Nat) :
    CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) -> Site 3
  | none => 0
  | some q => centralCylinderSite n q


def internalCentralPairCorrelation
    (beta : Real) (n m : Nat) (hnm : centralSquareSide n < m)
    (uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) ×
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n)) : Real :=
  multibondIsingTwoPoint cubicalDualEnds
    (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
      (oddCubeSide m) => beta)
    (internalCentralVertexEmbedding n m hnm uv.1)
    (internalCentralVertexEmbedding n m hnm uv.2)


end
end StatMech.FrontierA
