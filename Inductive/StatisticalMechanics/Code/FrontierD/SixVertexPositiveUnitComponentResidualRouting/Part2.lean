/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part7


namespace StatMech.FrontierD

noncomputable section

inductive SixVertexHorizontalResidualGeometricCertificate
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) : Type
  | fullMask
      (certificate : SixVertexHorizontalDegreeTwoLoopFullUnitMask source)
  | resolvedCross
      (cross : FKColoredResolvedUnitCross
        (sixVertexLoopDecoratedPairColored source.1))
  | fineRelated
      (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade)
      (related : SixVertexConfigurationPairTwoCycleFineRelated source.1.1
        target.1.1)

end
end StatMech.FrontierD
