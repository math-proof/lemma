/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootOffsetAbstract
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffset


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexCanonicalOddLowerHalfIndex (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    Fin ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) :=
  ⟨s + j, by omega⟩

def sixVertexCanonicalOddUpperHalfIndex (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    Fin ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) :=
  ⟨s + 1 + j, by omega⟩

def sixVertexCanonicalOddAlignedHalfRoots
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) : Real :=
  (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
      (sixVertexCanonicalOddLowerHalfIndex s k j) +
    sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
      (sixVertexCanonicalOddUpperHalfIndex s k j)) / 2

def sixVertexCanonicalOddChargeOffset
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) : Real :=
  (sixVertexFourWidth (2 * s + 1) k : Real) *
    (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j -
      sixVertexCanonicalOddAlignedHalfRoots hc s k j)

def sixVertexCanonicalOddOffsetBoundarySource
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) : Real :=
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let xL := p (sixVertexCanonicalOddLowerHalfIndex s k j)
  let xU := p (sixVertexCanonicalOddUpperHalfIndex s k j)
  ((∑ l, sixVertexTheta c xL (p l)) +
    (∑ l, sixVertexTheta c xU (p l))) / 2 -
      ∑ l, sixVertexTheta c
        (sixVertexCanonicalOddAlignedHalfRoots hc s k j)
        (sixVertexCanonicalOddAlignedHalfRoots hc s k l)

def sixVertexCanonicalOddOffsetNodalResidual
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) : Real :=
  let N := sixVertexFourWidth (2 * s + 1) k
  let p := sixVertexCanonicalOddAlignedHalfRoots hc s k
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalOddChargeOffset hc s k
  eps j - sixVertexCanonicalOddOffsetBoundarySource hc s k j +
    (1 / (N : Real)) * ∑ l,
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)

end
end StatMech.FrontierD
