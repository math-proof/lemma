/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFinite
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexEvenChargeBetheOffset
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) : Real :=
  (sixVertexFourWidth (2 * s) k : Real) *
    (sixVertexFixedChargeBetheRoots hc (2 * s) k j -
      sixVertexHalfFilledBetheRoots hc (2 * s + k)
        (sixVertexEvenChargeHalfIndex s k j))


def sixVertexOddChargeBetheOffset
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) : Real :=
  (sixVertexFourWidth (2 * s + 1) k : Real) *
    (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j -
      (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
          (sixVertexOddChargeLowerHalfIndex s k j) +
        sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
          (sixVertexOddChargeUpperHalfIndex s k j)) / 2)


end
end StatMech.FrontierD
