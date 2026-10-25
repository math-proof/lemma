/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootOffsetAbstract


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexCanonicalEvenHalfIndex (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    Fin ((2 * s + k + 1) + (2 * s + k + 1)) :=
  ⟨s + j, by omega⟩

def sixVertexCanonicalEvenAlignedHalfRoots
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) : Real :=
  sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)
    (sixVertexCanonicalEvenHalfIndex s k j)

def sixVertexCanonicalEvenChargeOffset
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) : Real :=
  (sixVertexFourWidth (2 * s) k : Real) *
    (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j -
      sixVertexCanonicalEvenAlignedHalfRoots hc s k j)

def sixVertexCanonicalEvenOffsetBoundarySource
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) : Real :=
  (∑ l, sixVertexTheta c
      (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
      (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k) l)) -
    ∑ l, sixVertexTheta c
      (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
      (sixVertexCanonicalEvenAlignedHalfRoots hc s k l)

def sixVertexCanonicalEvenOffsetNodalResidual
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) : Real :=
  let N := sixVertexFourWidth (2 * s) k
  let p := sixVertexCanonicalEvenAlignedHalfRoots hc s k
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalEvenChargeOffset hc s k
  eps j - sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
    (1 / (N : Real)) * ∑ l,
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)

end
end StatMech.FrontierD
