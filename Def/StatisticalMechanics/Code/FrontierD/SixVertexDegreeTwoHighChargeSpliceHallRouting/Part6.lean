/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part4


namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets

noncomputable def pairedInverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      targets.PairedRelated source target} ↪ Fin 2 where
  toFun source := finTwoEquiv.symm
    (targets.pairedInverseBranch target source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hbranch : targets.pairedInverseBranch target first =
        targets.pairedInverseBranch target second := by
      apply finTwoEquiv.symm.injective
      exact heq
    have htarget : first.1 = second.1 := by
      apply targets.target_injective
        (targets.pairedInverseBranch target first)
      calc
        sixVertexHorizontalDegreeTwoLoopSpliceTarget first.1.1
            (targets.branchKey first.1
              (targets.pairedInverseBranch target first)) = target :=
          targets.paired_inverse_spec target first
        _ = sixVertexHorizontalDegreeTwoLoopSpliceTarget second.1.1
            (targets.branchKey second.1
              (targets.pairedInverseBranch target second)) :=
          (targets.paired_inverse_spec target second).symm
        _ = sixVertexHorizontalDegreeTwoLoopSpliceTarget second.1.1
            (targets.branchKey second.1
              (targets.pairedInverseBranch target first)) := by rw [hbranch]
    exact htarget

end SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
end
end StatMech.FrontierD
