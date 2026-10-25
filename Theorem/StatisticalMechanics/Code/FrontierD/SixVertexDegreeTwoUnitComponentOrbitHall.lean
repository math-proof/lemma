/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDegreeTwoUnitStrandPhysicalRelated.fineRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt}
    {target : SixVertexConfigurationPhysicalTarget T middle}
    (hrelated : SixVertexDegreeTwoUnitStrandPhysicalRelated source target) :
    sixVertexPairAtMostTwoCycleFineRelated
      (source.1.1, source.2.1) (target.1.1, target.2.1) := by
  obtain ⟨hdegree, seed, hunit, rfl⟩ := hrelated
  exact sixVertexDegreeTwoUnitStrandPhysicalTarget_fineRelated
    source hdegree seed hunit


theorem SixVertexDegreeTwoUnitStrandPhysicalRelated.layers_ne
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt}
    {target : SixVertexConfigurationPhysicalTarget T middle}
    (hrelated : SixVertexDegreeTwoUnitStrandPhysicalRelated source target) :
    target.1 ≠ target.2 := by
  obtain ⟨hdegree, seed, hunit, rfl⟩ := hrelated
  exact sixVertexDegreeTwoUnitStrandPhysicalTarget_layers_ne
    source hdegree seed hunit


end
end StatMech.FrontierD
