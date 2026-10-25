/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteCumulativeGradeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem TwoBranchMonotoneEmbeddings.inverse_degree
    {Source Target : Type*} [Fintype Source]
    {sourceGrade : Source → Nat} {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (target : Target) :
    (Finset.univ.filter fun source => embeddings.Related source target).card ≤
      2 := by
  have hcard := Fintype.card_le_of_embedding (embeddings.inverseCode target)
  simpa [Fintype.card_subtype] using hcard

theorem TwoBranchMonotoneEmbeddings.upperCumulative
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    {sourceGrade : Source → Nat} {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) :
    ∀ grade,
      (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤
        (Finset.univ.filter fun target => grade ≤ targetGrade target).card :=
  finiteUpperCumulative_of_twoBranchCapacity embeddings.Related sourceGrade
    targetGrade embeddings.forward_degree embeddings.inverse_degree
    (by
      intro source target hrelated
      obtain ⟨choice, rfl⟩ := hrelated
      exact embeddings.monotone choice source)

theorem TwoBranchMonotoneEmbeddings.exists_injective_gradeMonotone
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    {sourceGrade : Source → Nat} {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) :
    ∃ matching : Source → Target,
      Function.Injective matching ∧
        ∀ source, sourceGrade source ≤ targetGrade (matching source) :=
  exists_injective_gradeMonotone_of_upperCumulative sourceGrade targetGrade
    embeddings.upperCumulative

end
end StatMech.FrontierD
