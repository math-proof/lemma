/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualOddPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerron
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetReduction.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexEventuallyOddChargeBethePerronIdentification
    {c : Real} (hc : 2 < c) (r : Nat) : Prop :=
  ∀ᶠ k : Nat in atTop,
    sixVertexFixedOddChargeBetheEigenvalueValue hc r k =
      sixVertexLambdaAlongFour c r k

end
end StatMech.FrontierD
