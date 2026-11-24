module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part6
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedInverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade)
    (source : {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      reconnection.PairedRelated source target}) : Bool :=
  Classical.choose source.2

end
end StatMech.FrontierD
