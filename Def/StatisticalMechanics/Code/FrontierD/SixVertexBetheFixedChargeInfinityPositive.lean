/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPositive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityNonzero
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityPositive
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeLimitingSineProduct (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) : Real :=
  ∏ i, ∏ j ∈ Finset.Ioi i,
    2 * Real.sin
      (Real.pi *
        ((sixVertexFixedChargeAlternantExponent r k x j : Real) -
          sixVertexFixedChargeAlternantExponent r k x i) /
        (sixVertexFixedChargeBetheComplementCount r k : Real))


def sixVertexFixedChargeBethePairCount (r k : Nat) : Nat :=
  ∑ i : Fin (sixVertexFixedChargeBetheParticleCount r k),
    (Finset.Ioi i).card

end
end StatMech.FrontierD
