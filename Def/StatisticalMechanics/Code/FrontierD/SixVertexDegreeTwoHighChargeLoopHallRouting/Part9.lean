/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedInverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      reconnection.PairedRelated source target} ↪ Fin 2 where
  toFun source := finTwoEquiv.symm
    (reconnection.pairedInverseBranch target source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hbranch : reconnection.pairedInverseBranch target first =
        reconnection.pairedInverseBranch target second := by
      apply finTwoEquiv.symm.injective
      exact heq
    apply reconnection.paired_branch_injective
      (reconnection.pairedInverseBranch target first)
    calc
      sixVertexHorizontalDegreeTwoLoopRoutedTarget first.1.1
          (reconnection.key first.1.1
            (reconnection.pairedInverseBranch target first)) = target :=
        reconnection.paired_inverse_spec target first
      _ = sixVertexHorizontalDegreeTwoLoopRoutedTarget second.1.1
          (reconnection.key second.1.1
            (reconnection.pairedInverseBranch target second)) :=
        (reconnection.paired_inverse_spec target second).symm
      _ = sixVertexHorizontalDegreeTwoLoopRoutedTarget second.1.1
          (reconnection.key second.1.1
            (reconnection.pairedInverseBranch target first)) := by rw [hbranch]

end
end StatMech.FrontierD
