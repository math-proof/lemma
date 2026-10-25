/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part4


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

structure HexEndpointCyclicLoopPair (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  baseLabel : Fin 3
  base : List ℤ
  loopQ : List ℤ
  loopQ_first : ∃ tail, loopQ = 1 :: tail
  loopQ_sum : loopQ.sum = -4
  succ_valid :
    (ofTurns a h0 (base ++ loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ loopQ)).EndsAt
        (labelMid v du (hexCyclicSucc baseLabel))
  pred_valid :
    (ofTurns a h0 (base ++ hexEndpointLoopPartner loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ hexEndpointLoopPartner loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ hexEndpointLoopPartner loopQ)).EndsAt
        (labelMid v du (hexCyclicPred baseLabel))

end
end StatMech.Universality
