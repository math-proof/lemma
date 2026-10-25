/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTaylor


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexEvenChargeAlignedHalfRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) → Real :=
  fun j => sixVertexHalfFilledBetheRoots hc (2 * s + k)
    (sixVertexEvenChargeHalfIndex s k j)


def sixVertexEvenChargeOffsetBoundarySource
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) : Real :=
  (∑ l, sixVertexTheta c
      (sixVertexEvenChargeAlignedHalfRoots hc s k j)
      (sixVertexHalfFilledBetheRoots hc (2 * s + k) l)) -
    ∑ l, sixVertexTheta c
      (sixVertexEvenChargeAlignedHalfRoots hc s k j)
      (sixVertexEvenChargeAlignedHalfRoots hc s k l)


def sixVertexEvenChargeOffsetNodalResidual
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) : Real :=
  let N : Real := sixVertexFourWidth (2 * s) k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let eps := sixVertexEvenChargeBetheOffset hc s k
  eps j - sixVertexEvenChargeOffsetBoundarySource hc s k j +
    (1 / N) * ∑ l, (
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)

end
end StatMech.FrontierD
