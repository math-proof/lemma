/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTaylor
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFiniteResidual


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexOddChargeAlignedHalfRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) → Real :=
  fun j =>
    (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
          (sixVertexOddChargeLowerHalfIndex s k j) +
        sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
          (sixVertexOddChargeUpperHalfIndex s k j)) / 2


def sixVertexOddChargeOffsetBoundarySource
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) : Real :=
  let pl := sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
  ((∑ l, sixVertexTheta c
        (pl (sixVertexOddChargeLowerHalfIndex s k j)) (pl l)) +
      (∑ l, sixVertexTheta c
        (pl (sixVertexOddChargeUpperHalfIndex s k j)) (pl l))) / 2 -
    ∑ l, sixVertexTheta c
      (sixVertexOddChargeAlignedHalfRoots hc s k j)
      (sixVertexOddChargeAlignedHalfRoots hc s k l)


def sixVertexOddChargeOffsetNodalResidual
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) : Real :=
  let N : Real := sixVertexFourWidth (2 * s + 1) k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let eps := sixVertexOddChargeBetheOffset hc s k
  eps j - sixVertexOddChargeOffsetBoundarySource hc s k j +
    (1 / N) * ∑ l, (
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)

end
end StatMech.FrontierD
