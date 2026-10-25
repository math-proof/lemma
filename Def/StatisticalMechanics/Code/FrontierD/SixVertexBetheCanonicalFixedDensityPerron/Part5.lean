/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part4


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def SixVertexCanonicalFixedOddDensityWitness
    {c : Real} (hc : 2 < c) (s k : Nat)
    (p : Fin (((s + k + 1) + 1) + (s + k + 1)) -> Real) : Prop :=
  SixVertexFixedOddChargePerronBranchWitness c s k p ∧
    forall x, sixVertexCanonicalFixedOddDensityFloor hc s <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1)) p x

end
end StatMech.FrontierD
