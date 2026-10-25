/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

structure SixVertexHorizontalDegreeTwoRecoverableReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  target : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade → Bool →
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade
  source_recoverable : ∀ first firstBranch second secondBranch,
    target first firstBranch = target second secondBranch → first = second
  direct_supported : ∀ source :
      SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (target source.1 false)
  paired_distinct : ∀ source :
      SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    target source.1 false ≠ target source.1 true
  paired_supported : ∀ source :
      SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    ∀ branch,
      sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
        hmiddle_pos hmiddle_lt grade source.1 (target source.1 branch)


structure SixVertexHorizontalDegreeTwoHighChargeHallRouting
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  direct : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade →
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade
  direct_injective : Function.Injective direct
  direct_supported : ∀ source,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (direct source)
  paired : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade → Bool →
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade
  paired_distinct : ∀ source, paired source false ≠ paired source true
  paired_supported : ∀ source branch,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (paired source branch)
  paired_output_recovers_occurrence : ∀ branch first second,
    paired first branch = paired second branch →
      sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first =
        sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second
  paired_injective_with_occurrence : ∀ branch first second,
    sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first =
        sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second →
      paired first branch = paired second branch → first = second
  direct_paired_disjoint : ∀ directSource pairedSource branch,
    direct directSource ≠ paired pairedSource branch


end
end StatMech.FrontierD
