/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronClosed
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualOddPerron
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  if _hr : Even r then
    sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc (r / 2) k
  else
    sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc ((r - 1) / 2) k


def SixVertexEventuallyFixedChargeBethePerronIdentification
    {c : Real} (hc : 2 < c) (r : Nat) : Prop :=
  ∀ᶠ k : Nat in atTop,
    sixVertexFixedChargeBetheEigenvalueValue hc r k =
      sixVertexLambdaAlongFour c r k

def SixVertexEventuallyEvenChargeBethePerronIdentification
    {c : Real} (hc : 2 < c) (s : Nat) : Prop :=
  ∀ᶠ k : Nat in atTop,
    sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc s k =
      sixVertexLambdaAlongFour c (2 * s) k

end
end StatMech.FrontierD
