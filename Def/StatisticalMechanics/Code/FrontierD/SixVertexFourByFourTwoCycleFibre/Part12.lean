/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part11


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedParamTargetFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam : Fin 4) (column : Fin 4) :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourToggleVerticalColumn
    column
    (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)

def sixVertexFourByFourAuditedParamTargetSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (secondSeam : Fin 4) (column : Fin 4) :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourToggleVerticalColumn
    column
    (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)

def SixVertexFourByFourValidColumnRepair
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) (columns : Fin 4 × Fin 4) : Prop :=
  (sixVertexFourByFourAuditedParamTargetFirst
      p firstSeam columns.1).IceRule /\
    (sixVertexFourByFourAuditedParamTargetSecond
      p secondSeam columns.2).IceRule /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedParamTargetFirst
            p firstSeam columns.1)
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedParamTargetSecond
            p secondSeam columns.2)
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2

def SixVertexFourByFourAuditedParamMatchingStatement
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) : Prop :=
  (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).IceRule ->
  (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).IceRule ->
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 ->
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 3 ->
    SixVertexFourByFourValidColumnRepair p firstSeam secondSeam
      (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam)

def SixVertexFourByFourAuditedSelectedColumnsConstantStatement
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) : Prop :=
  (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).IceRule ->
  (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).IceRule ->
  sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 ->
  sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 3 ->
  (forall y,
      (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).vertical
        ((sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).1, y) =
          false) /\
    (forall y,
      (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).vertical
        ((sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2, y) =
          true)

end
end StatMech.FrontierD
