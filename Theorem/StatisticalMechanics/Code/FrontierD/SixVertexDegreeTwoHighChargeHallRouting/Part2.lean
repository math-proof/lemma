/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalDegreeTwoHighCharge_seed
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    let pair := sixVertexHorizontalActualDeficitConfigurationPair source.1
    ∃ hdegree : SixVertexLocallyDegreeTwo pair.1.1.1 pair.1.2.1,
      ∃ component :
          (sixVertexDegreeTwoSynchronizedGraph pair.1.1.2.1 pair.1.2.2.1
            hdegree).ConnectedComponent,
        Nonempty (SixVertexDegreeTwoSynchronizedHighChargeSeed
          pair.1.1.2.1 pair.1.2.2.1 hdegree component) := by
  dsimp only
  rcases source.2 with ⟨hdegree, component, hcharge⟩
  exact ⟨hdegree, component,
    sixVertexDegreeTwoSynchronizedHighChargeSeed_nonempty
      _ _ hdegree component hcharge⟩


end
end StatMech.FrontierD
