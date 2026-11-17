/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part7


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

public noncomputable section

structure HexEndpointCyclicTriplet (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (v du : ℂ) where
  baseLabel : Fin 3
  base : List ℤ
  base_valid :
    (ofTurns a h0 base).EndpointIsLegalSAW ∧
      (ofTurns a h0 base).StaysIn region ∧
      (ofTurns a h0 base).EndsAt (labelMid v du baseLabel)
  succ_valid :
    (ofTurns a h0 (base ++ [-1])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ [-1])).StaysIn region ∧
      (ofTurns a h0 (base ++ [-1])).EndsAt
        (labelMid v du (hexCyclicSucc baseLabel))
  pred_valid :
    (ofTurns a h0 (base ++ [1])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ [1])).StaysIn region ∧
      (ofTurns a h0 (base ++ [1])).EndsAt
        (labelMid v du (hexCyclicPred baseLabel))

end
end StatMech.Universality
