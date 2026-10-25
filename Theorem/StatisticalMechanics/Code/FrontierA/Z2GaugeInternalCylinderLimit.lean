/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

@[simp] theorem internalCentralVertexEmbedding_none
    (n m : Nat) (hnm : centralSquareSide n < m) :
    internalCentralVertexEmbedding n m hnm none = none := rfl

@[simp] theorem internalCentralVertexEmbedding_some
    (n m : Nat) (hnm : centralSquareSide n < m)
    (q : CubicalCell (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :
    internalCentralVertexEmbedding n m hnm (some q) =
      some (internalCentralCellEmbedding n m hnm q) := rfl


end
end StatMech.FrontierA
