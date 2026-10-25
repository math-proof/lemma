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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part3
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem configurationPairTotalCReconnection_iff_fiberDominates
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) :
    SixVertexConfigurationPairTotalCReconnection T lower middle upper <->
      SixVertexConfigurationPairTotalCFiberDominates
        T lower middle upper :=
  exists_injective_gradePreserving_iff_fiberCard
    sixVertexConfigurationPairTotalC sixVertexConfigurationPairTotalC


theorem decoratedTotalCFiberDominates_of_configurationPair
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hfiber : SixVertexConfigurationPairTotalCFiberDominates
      T lower middle upper) (k : Nat) :
    SixVertexMarkedDecoratedPairTotalCFiberDominates
      T lower middle upper k := by
  intro total
  rw [card_sixVertexMarkedDecoratedPairTotalCFiber,
    card_sixVertexMarkedDecoratedPairTotalCFiber]
  exact Nat.mul_le_mul_right _ (hfiber total)


theorem exists_injective_equalTotalC_of_fiberDominates
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (hfiber : SixVertexMarkedDecoratedPairTotalCFiberDominates
      T lower middle upper k) :
    exists matching : SixVertexMarkedDecoratedPair T lower upper k ->
        SixVertexMarkedDecoratedPair T middle middle k,
      Function.Injective matching /\
        forall source,
          SixVertexMarkedDecoratedPairEqualTotalC source (matching source) := by
  let embedding : forall total : Nat,
      {source : SixVertexMarkedDecoratedPair T lower upper k //
        sixVertexMarkedDecoratedPairTotalC source = total} ↪
      {target : SixVertexMarkedDecoratedPair T middle middle k //
        sixVertexMarkedDecoratedPairTotalC target = total} :=
    fun total => Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr (hfiber total))
  let gradedEmbedding :
      (Sigma fun total : Nat =>
        {source : SixVertexMarkedDecoratedPair T lower upper k //
          sixVertexMarkedDecoratedPairTotalC source = total}) ↪
      (Sigma fun total : Nat =>
        {target : SixVertexMarkedDecoratedPair T middle middle k //
          sixVertexMarkedDecoratedPairTotalC target = total}) :=
    { toFun := fun graded =>
        ⟨graded.1, embedding graded.1 graded.2⟩
      inj' := by
        rintro ⟨total₁, source₁⟩ ⟨total₂, source₂⟩ heq
        have htotal : total₁ = total₂ := congrArg Sigma.fst heq
        subst total₂
        have hfiberEq :
            embedding total₁ source₁ = embedding total₁ source₂ := by
          exact eq_of_heq (Sigma.mk.inj heq).2
        have hsource := (embedding total₁).injective hfiberEq
        cases hsource
        rfl }
  let matchingEmbedding :
      SixVertexMarkedDecoratedPair T lower upper k ↪
        SixVertexMarkedDecoratedPair T middle middle k :=
    (Equiv.sigmaFiberEquiv
      (fun source : SixVertexMarkedDecoratedPair T lower upper k =>
        sixVertexMarkedDecoratedPairTotalC source)).symm.toEmbedding |>.trans
      (gradedEmbedding.trans
        (Equiv.sigmaFiberEquiv
          (fun target : SixVertexMarkedDecoratedPair T middle middle k =>
            sixVertexMarkedDecoratedPairTotalC target)).toEmbedding)
  refine ⟨matchingEmbedding, matchingEmbedding.injective, ?_⟩
  intro source
  exact (embedding (sixVertexMarkedDecoratedPairTotalC source)
    ⟨source, rfl⟩).2.symm


theorem sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (hfiber : SixVertexMarkedDecoratedPairTotalCFiberDominates
      T lower middle upper k) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k
      SixVertexMarkedDecoratedPairEqualTotalC := by
  rw [sixVertexMarkedDecoratedPairHall_iff_exists_injective]
  exact exists_injective_equalTotalC_of_fiberDominates hfiber


theorem sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hfiber : SixVertexConfigurationPairTotalCFiberDominates
      T lower middle upper) (k : Nat) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k
      SixVertexMarkedDecoratedPairEqualTotalC :=
  sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates
    (decoratedTotalCFiberDominates_of_configurationPair hfiber k)


theorem sixVertexMarkedDecoratedPairHall_equalTotalC_of_reconnection
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hreconnect : SixVertexConfigurationPairTotalCReconnection
      T lower middle upper) (k : Nat) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k
      SixVertexMarkedDecoratedPairEqualTotalC :=
  sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair
    ((configurationPairTotalCReconnection_iff_fiberDominates
      T lower middle upper).mp hreconnect) k


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexConfigurationPairTotalCFiberDominates T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_decoratedHall
    T middle hmiddle_pos hmiddle_lt
  intro k
  exact ⟨SixVertexMarkedDecoratedPairEqualTotalC,
    sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair
      hfiber k⟩


theorem sixVertexSectorTrace_logConcave_of_totalCFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hfiber : SixVertexConfigurationPairTotalCFiberDominates T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
  exact sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    T.width T.height middle.val hc
      (sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers
      T middle hmiddle_pos hmiddle_lt hfiber)


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hreconnect : SixVertexConfigurationPairTotalCReconnection T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers
    T middle hmiddle_pos hmiddle_lt
      ((configurationPairTotalCReconnection_iff_fiberDominates T
        ⟨middle.val - 1, by omega⟩ middle
        ⟨middle.val + 1, by omega⟩).mp hreconnect)


theorem sixVertexMarkedDecoratedPairHall_equalTotalC_iff_fiberDominates
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) (k : Nat) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k
        SixVertexMarkedDecoratedPairEqualTotalC <->
      SixVertexMarkedDecoratedPairTotalCFiberDominates
        T lower middle upper k := by
  constructor
  · intro hall total
    obtain ⟨matching, hinjective, hrelated⟩ :=
      (sixVertexMarkedDecoratedPairHall_iff_exists_injective
        T lower middle upper k SixVertexMarkedDecoratedPairEqualTotalC).mp hall
    let fiberEmbedding :
        {source : SixVertexMarkedDecoratedPair T lower upper k //
          sixVertexMarkedDecoratedPairTotalC source = total} ↪
        {target : SixVertexMarkedDecoratedPair T middle middle k //
          sixVertexMarkedDecoratedPairTotalC target = total} :=
      { toFun := fun source =>
          ⟨matching source.1,
            (hrelated source.1).symm.trans source.2⟩
        inj' := by
          intro source₁ source₂ heq
          apply Subtype.ext
          apply hinjective
          exact congrArg Subtype.val heq }
    exact Fintype.card_le_of_embedding fiberEmbedding
  · exact sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates


theorem sixVertexFourByTwo_reconnection_equalTotalC :
    sixVertexTorusCTypeCount sixVertexFourByTwoLowArrows +
        sixVertexTorusCTypeCount sixVertexFourByTwoHighArrows =
      sixVertexTorusCTypeCount sixVertexFourByTwoMiddleArrows +
        sixVertexTorusCTypeCount sixVertexFourByTwoMiddleArrows := by
  rw [sixVertexFourByTwoLowArrows_cTypeCount,
    sixVertexFourByTwoHighArrows_cTypeCount,
    sixVertexFourByTwoMiddleArrows_cTypeCount]

end
end StatMech.FrontierD
