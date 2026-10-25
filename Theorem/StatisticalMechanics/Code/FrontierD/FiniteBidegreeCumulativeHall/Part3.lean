/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteCumulativeGradeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem TwoBranchMonotoneEmbeddings.branch_inverseChoice
    {Source Target : Type*} {sourceGrade : Source → Nat}
    {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (target : Target)
    (source : {source : Source // embeddings.Related source target}) :
    embeddings.branch (embeddings.inverseChoice target source) source.1 =
      target :=
  Classical.choose_spec source.2

end
end StatMech.FrontierD
