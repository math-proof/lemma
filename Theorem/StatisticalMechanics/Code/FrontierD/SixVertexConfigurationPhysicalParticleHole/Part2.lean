/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPhysicalParticleHoleMiddle_pos
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_lt : middle.val < T.width) :
    0 < (sixVertexPhysicalParticleHoleMiddle middle).val := by
  simp [sixVertexPhysicalParticleHoleMiddle]
  omega

theorem sixVertexPhysicalParticleHoleMiddle_lt
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) :
    (sixVertexPhysicalParticleHoleMiddle middle).val < T.width := by
  have hwidth := T.width_pos
  have hmiddle_le : middle.val ≤ T.width := by omega
  have hcancel : T.width - middle.val + middle.val = T.width :=
    Nat.sub_add_cancel hmiddle_le
  simp only [sixVertexPhysicalParticleHoleMiddle]
  omega

end
end StatMech.FrontierD
