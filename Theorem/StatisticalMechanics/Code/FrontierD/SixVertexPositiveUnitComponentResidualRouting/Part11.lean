/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part13


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentResidualMixedRouting

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


theorem decode_direct
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    routing.decoder (routing.direct source) = some source.1 := by
  by_cases hrealizable :
      sixVertexPositiveUnitComponentResidualSource source.1
  · rw [direct, dif_pos hrealizable]
    exact routing.decode_unit (nonHighToUnit source hrealizable)
  · rw [direct, dif_neg hrealizable]
    exact routing.decode_geometric
      (nonHighToGeometric source hrealizable)

theorem direct_supported
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (routing.direct source) := by
  by_cases hrealizable :
      sixVertexPositiveUnitComponentResidualSource source.1
  · rw [direct, dif_pos hrealizable]
    exact routing.unit.matching_supported
      (nonHighToUnit source hrealizable)
  · rw [direct, dif_neg hrealizable]
    exact routing.geometric_supported
      (nonHighToGeometric source hrealizable)

theorem direct_injective
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective routing.direct := by
  intro first second heq
  have hdecoded := congrArg routing.decoder heq
  rw [routing.decode_direct first, routing.decode_direct second] at hdecoded
  apply Subtype.ext
  exact Option.some.inj hdecoded

theorem direct_paired_disjoint
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (directSource : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (pairedSource : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    routing.direct directSource ≠ routing.paired pairedSource branch := by
  intro heq
  have hdecoded := congrArg routing.decoder heq
  simp only [paired] at hdecoded
  rw [routing.decode_direct directSource,
    routing.decode_paired pairedSource branch] at hdecoded
  have hsource : directSource.1 = pairedSource.1 := Option.some.inj hdecoded
  exact directSource.2 (hsource ▸ pairedSource.2)


end SixVertexPositiveUnitComponentResidualMixedRouting
end
end StatMech.FrontierD
