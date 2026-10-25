/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteCumulativeGradeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem TwoBranchMonotoneEmbeddings.forward_degree
    {Source Target : Type*} [Fintype Target]
    {sourceGrade : Source → Nat} {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (source : Source) :
    2 ≤ (Finset.univ.filter (embeddings.Related source)).card := by
  let certificates : Fin 2 ↪ {target : Target // embeddings.Related source target} :=
    { toFun := fun choice =>
        ⟨embeddings.branch (finTwoEquiv choice) source,
          ⟨finTwoEquiv choice, rfl⟩⟩
      inj' := by
        intro first second heq
        apply finTwoEquiv.injective
        cases hfirst : finTwoEquiv first <;>
          cases hsecond : finTwoEquiv second
        · rfl
        · exact False.elim (embeddings.distinct source (by
            simpa [hfirst, hsecond] using congrArg Subtype.val heq))
        · exact False.elim (embeddings.distinct source (by
            simpa [hfirst, hsecond] using (congrArg Subtype.val heq).symm))
        · rfl }
  have hcard := Fintype.card_le_of_embedding certificates
  simpa [Fintype.card_subtype] using hcard

end
end StatMech.FrontierD
