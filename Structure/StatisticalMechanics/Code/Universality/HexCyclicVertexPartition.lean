/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


structure HexCyclicTriplet (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  baseLabel : Fin 3
  base : List ℤ
  base_valid :
    (ofTurns a h0 base).IsLegalSAW ∧
      (ofTurns a h0 base).StaysIn region ∧
      (ofTurns a h0 base).EndsAt (labelMid v du baseLabel)
  succ_valid :
    (ofTurns a h0 (base ++ [-1])).IsLegalSAW ∧
      (ofTurns a h0 (base ++ [-1])).StaysIn region ∧
      (ofTurns a h0 (base ++ [-1])).EndsAt
        (labelMid v du (hexCyclicSucc baseLabel))
  pred_valid :
    (ofTurns a h0 (base ++ [1])).IsLegalSAW ∧
      (ofTurns a h0 (base ++ [1])).StaysIn region ∧
      (ofTurns a h0 (base ++ [1])).EndsAt
        (labelMid v du (hexCyclicPred baseLabel))


end
end StatMech.Universality
