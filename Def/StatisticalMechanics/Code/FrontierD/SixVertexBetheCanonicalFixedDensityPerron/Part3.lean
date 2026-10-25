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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part2


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

noncomputable def sixVertexCanonicalFixedEvenDensityPerronBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin ((s + k + 1) + (s + k + 1)) -> Real := by
  classical
  exact if h : ∃ p, SixVertexCanonicalFixedEvenDensityWitness hc s k p then
    Classical.choose h
  else sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k

end
end StatMech.FrontierD
