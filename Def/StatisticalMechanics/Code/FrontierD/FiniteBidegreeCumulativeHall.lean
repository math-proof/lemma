/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteCumulativeGradeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Structure.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall
open Finset


namespace StatMech.FrontierD

noncomputable section

def TwoBranchMonotoneEmbeddings.Related
    {Source Target : Type*} {sourceGrade : Source → Nat}
    {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (source : Source) (target : Target) : Prop :=
  ∃ choice, embeddings.branch choice source = target

end
end StatMech.FrontierD
