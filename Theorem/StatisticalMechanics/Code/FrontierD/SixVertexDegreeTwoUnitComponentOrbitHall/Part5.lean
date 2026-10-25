/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDegreeTwoUnitComponentOrbitPresentation

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Component : Type*} [Fintype Component] {k : Nat}


theorem hall
    (orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt Component k) : orbit.Hall := by
  have hBoolean := booleanMiddleLayerDownRelation_hall k orbit.component_card
  obtain ⟨matching, hinjective, hmatching⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (booleanMiddleLayerDownRelation
        (Component := Component) (k := k))).mp hBoolean
  let physicalMatching : orbit.SourceOrbit -> orbit.TargetOrbit :=
    fun source => orbit.targetEquiv (matching (orbit.sourceEquiv.symm source))
  have hphysicalInjective : Function.Injective physicalMatching := by
    intro first second heq
    apply orbit.sourceEquiv.symm.injective
    apply hinjective
    apply orbit.targetEquiv.injective
    exact heq
  have hphysicalRelated : forall source, orbit.Related source
      (physicalMatching source) := by
    intro source
    let booleanSource := orbit.sourceEquiv.symm source
    have hrel := hmatching booleanSource
    have := (orbit.related_equiv booleanSource
      (matching booleanSource)).2 hrel
    simpa [physicalMatching, booleanSource] using this
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective orbit.Related).2
    ⟨physicalMatching, hphysicalInjective, hphysicalRelated⟩

end SixVertexDegreeTwoUnitComponentOrbitPresentation
end
end StatMech.FrontierD
