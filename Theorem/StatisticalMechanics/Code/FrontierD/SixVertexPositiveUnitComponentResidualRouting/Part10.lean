/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentResidualMixedRouting

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


theorem unit_paired_disjoint
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (unitSource : SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (highSource : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    routing.unit.matching unitSource ≠ routing.paired highSource branch := by
  intro heq
  have hdecoded := congrArg routing.decoder heq
  simp only [paired] at hdecoded
  rw [routing.decode_unit unitSource,
    routing.decode_paired highSource branch] at hdecoded
  have hsource : unitSource.1 = highSource.1 := Option.some.inj hdecoded
  exact unitSource.2.2 (hsource ▸ highSource.2)


end SixVertexPositiveUnitComponentResidualMixedRouting
end
end StatMech.FrontierD
