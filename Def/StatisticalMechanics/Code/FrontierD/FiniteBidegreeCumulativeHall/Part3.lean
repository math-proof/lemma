/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteCumulativeGradeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def TwoBranchMonotoneEmbeddings.inverseCode
    {Source Target : Type*} {sourceGrade : Source → Nat}
    {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (target : Target) :
    {source : Source // embeddings.Related source target} ↪ Fin 2 where
  toFun source := finTwoEquiv.symm (embeddings.inverseChoice target source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hchoice : embeddings.inverseChoice target first =
        embeddings.inverseChoice target second := by
      apply finTwoEquiv.symm.injective
      exact heq
    apply (embeddings.branch (embeddings.inverseChoice target first)).injective
    calc
      embeddings.branch (embeddings.inverseChoice target first) first.1 =
          target := embeddings.branch_inverseChoice target first
      _ = embeddings.branch (embeddings.inverseChoice target second) second.1 :=
        (embeddings.branch_inverseChoice target second).symm
      _ = embeddings.branch (embeddings.inverseChoice target first) second.1 := by
        rw [hchoice]

end
end StatMech.FrontierD
