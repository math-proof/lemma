/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part10


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

structure HexEndpointLoopPair (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  base : List ℤ
  loopQ : List ℤ
  loopQ_sum : loopQ.sum = -4
  q_valid :
    (ofTurns a h0 (base ++ loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ loopQ)).EndsAt (v + hexOmega * du)
  r_valid :
    (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).EndsAt
        (v + hexOmega ^ 2 * du)


structure HexEndpointLoopGeometry (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  base : List ℤ
  loopQ : List ℤ
  q_valid :
    (ofTurns a h0 (base ++ loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ loopQ)).EndsAt (v + hexOmega * du)
  reversed_saw :
    (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).EndpointIsSAW
  reversed_stay :
    (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).StaysIn region
  reversed_ends :
    (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).EndsAt
      (v + hexOmega ^ 2 * du)


end
end StatMech.Universality
