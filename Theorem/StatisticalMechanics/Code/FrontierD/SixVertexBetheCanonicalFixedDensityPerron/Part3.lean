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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part3


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      SixVertexCanonicalFixedEvenDensityWitness hc s k
        (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) := by
  filter_upwards
    [eventually_exists_sixVertexCanonicalFixedEvenDensityWitness hc s]
      with k hk
  rw [sixVertexCanonicalFixedEvenDensityPerronBetheRoots, dif_pos hk]
  exact Classical.choose_spec hk

end
end StatMech.FrontierD
