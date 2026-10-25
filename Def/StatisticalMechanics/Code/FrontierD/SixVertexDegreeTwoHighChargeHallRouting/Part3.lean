/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalDegreeTwoHighChargeWitness
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHighChargeWitness source := by
  apply Classical.choice
  rcases source.2 with ⟨hdegree, component, hcharge⟩
  exact ⟨⟨hdegree, component, hcharge⟩⟩

noncomputable def sixVertexHorizontalDegreeTwoHighChargeSeed
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :=
  let witness := sixVertexHorizontalDegreeTwoHighChargeWitness source
  sixVertexDegreeTwoSynchronizedHighChargeSeed
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.2.1
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.2.1
    witness.hdegree witness.component witness.charge


noncomputable def sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  (sixVertexHorizontalDegreeTwoHighChargeSeed source).occurrenceEquiv


end
end StatMech.FrontierD
