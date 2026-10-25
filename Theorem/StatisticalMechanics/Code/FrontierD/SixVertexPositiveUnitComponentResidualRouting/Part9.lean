/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part11


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentResidualMixedRouting

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


theorem paired_distinct
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    routing.paired source false ≠ routing.paired source true :=
  (routing.high source).target_distinct

theorem paired_supported
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) (branch : Bool) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1
        (routing.paired source branch) :=
  (routing.high source).target_supported branch


theorem paired_output_recovers_occurrence
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool)
    (first second : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (heq : routing.paired first branch = routing.paired second branch) :
    sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first =
      sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second := by
  have hdecoded := congrArg routing.decoder heq
  simp only [paired] at hdecoded
  rw [routing.decode_paired first branch,
    routing.decode_paired second branch] at hdecoded
  have hsource : first = second := by
    apply Subtype.ext
    exact Option.some.inj hdecoded
  rw [hsource]

theorem paired_injective_with_occurrence
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool)
    (first second : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (_ : sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first =
      sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second)
    (heq : routing.paired first branch = routing.paired second branch) :
    first = second := by
  have hdecoded := congrArg routing.decoder heq
  simp only [paired] at hdecoded
  rw [routing.decode_paired first branch,
    routing.decode_paired second branch] at hdecoded
  apply Subtype.ext
  exact Option.some.inj hdecoded


theorem geometric_injective
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective (fun source => (routing.geometric source).target) := by
  intro first second heq
  have hdecoded := congrArg routing.decoder heq
  rw [routing.decode_geometric first,
    routing.decode_geometric second] at hdecoded
  apply Subtype.ext
  exact Option.some.inj hdecoded


theorem geometric_supported
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1
        (routing.geometric source).target :=
  (routing.geometric source).supported


end SixVertexPositiveUnitComponentResidualMixedRouting
end
end StatMech.FrontierD
