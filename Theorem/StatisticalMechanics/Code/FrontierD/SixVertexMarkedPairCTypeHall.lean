/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairReconnectionWitness
import Mathlib.Data.Fintype.EquivFin
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem exists_injective_gradePreserving_iff_fiberCard
    {Source Target Grade : Type*} [Fintype Source] [Fintype Target]
    [DecidableEq Grade]
    (sourceGrade : Source -> Grade) (targetGrade : Target -> Grade) :
    (exists matching : Source -> Target,
        Function.Injective matching /\
          forall source, sourceGrade source = targetGrade (matching source)) <->
      forall grade : Grade,
        Fintype.card {source : Source // sourceGrade source = grade} <=
          Fintype.card {target : Target // targetGrade target = grade} := by
  constructor
  · rintro ⟨matching, hinjective, hgrade⟩ grade
    let fiberEmbedding :
        {source : Source // sourceGrade source = grade} ↪
          {target : Target // targetGrade target = grade} :=
      { toFun := fun source =>
          ⟨matching source.1, (hgrade source.1).symm.trans source.2⟩
        inj' := by
          intro source₁ source₂ heq
          apply Subtype.ext
          apply hinjective
          exact congrArg Subtype.val heq }
    exact Fintype.card_le_of_embedding fiberEmbedding
  · intro hfiber
    let embedding : forall grade : Grade,
        {source : Source // sourceGrade source = grade} ↪
          {target : Target // targetGrade target = grade} :=
      fun grade => Classical.choice
        (Function.Embedding.nonempty_iff_card_le.mpr (hfiber grade))
    let gradedEmbedding :
        (Sigma fun grade : Grade =>
          {source : Source // sourceGrade source = grade}) ↪
        (Sigma fun grade : Grade =>
          {target : Target // targetGrade target = grade}) :=
      { toFun := fun graded =>
          ⟨graded.1, embedding graded.1 graded.2⟩
        inj' := by
          rintro ⟨grade₁, source₁⟩ ⟨grade₂, source₂⟩ heq
          have hgrade : grade₁ = grade₂ := congrArg Sigma.fst heq
          subst grade₂
          have hfiberEq :
              embedding grade₁ source₁ = embedding grade₁ source₂ := by
            exact eq_of_heq (Sigma.mk.inj heq).2
          have hsource := (embedding grade₁).injective hfiberEq
          cases hsource
          rfl }
    let matchingEmbedding : Source ↪ Target :=
      (Equiv.sigmaFiberEquiv sourceGrade).symm.toEmbedding |>.trans
        (gradedEmbedding.trans
          (Equiv.sigmaFiberEquiv targetGrade).toEmbedding)
    refine ⟨matchingEmbedding, matchingEmbedding.injective, ?_⟩
    intro source
    exact (embedding (sourceGrade source) ⟨source, rfl⟩).2.symm


theorem exists_injective_bigradePreserving_iff_fiberCard
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (sourceGrade : Source -> Nat × Nat)
    (targetGrade : Target -> Nat × Nat) :
    (exists matching : Source -> Target,
        Function.Injective matching /\
          forall source, sourceGrade source = targetGrade (matching source)) <->
      forall grade : Nat × Nat,
        Fintype.card {source : Source // sourceGrade source = grade} <=
          Fintype.card {target : Target // targetGrade target = grade} :=
  exists_injective_gradePreserving_iff_fiberCard sourceGrade targetGrade


end
end StatMech.FrontierD
