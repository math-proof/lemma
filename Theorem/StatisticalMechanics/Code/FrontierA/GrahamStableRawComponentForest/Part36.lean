/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part36
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

theorem CanonicalStableRawComponentRichStrictBlock.closed_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          (∀ i, source ≠ block.sourceBlock i) ∧
          ∃ i, token = block.tokenPrefix i := by
  exact finiteRelationTokenClosed_or_crossing
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenPrefix


theorem CanonicalStableRawComponentRichStrictBlock.reducedDeficit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hclosed : block.IsClosed)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) <
      Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Fintype.card (FiniteEmbeddingComplement block.size block.tokenPrefix) <
        Fintype.card (FiniteEmbeddingComplement block.size block.sourceBlock) ∧
      (∃ extra : FiniteEmbeddingComplement block.size block.tokenPrefix,
        extra.1 = block.tokens (Fin.last block.size)) ∧
      ∀ source : FiniteEmbeddingComplement block.size block.sourceBlock,
        ∀ token,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token ->
            token ∉ finiteEmbeddingBlock block.size block.tokenPrefix := by
  refine ⟨finiteEmbeddingComplement_strictDeficit
      block.size block.sourceBlock block.tokenPrefix hdeficit, ?_, ?_⟩
  · let extra : FiniteEmbeddingComplement block.size block.tokenPrefix :=
      ⟨block.tokens (Fin.last block.size), by
        intro hmem
        obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
        exact Fin.castSucc_ne_last i (block.tokens.injective heq)⟩
    exact ⟨extra, rfl⟩
  · intro source token hincident
    exact finiteRelationComplement_tokenClosed
      (CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      block.size block.sourceBlock block.tokenPrefix hclosed
        source token hincident


theorem
    CanonicalStableRawComponentRichStrictBlock.crossingClassification
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token)
    (hsource : ∀ i, source ≠ block.sourceBlock i)
    (index : Fin block.size) (htoken : token = block.tokenPrefix index) :
    (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  have htokenDirect : token =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (block.directs index) := by
    exact htoken.trans (block.aligned index)
  have hsourceIncident : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1 source.1 := hincident
  have hdirectIncident : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1
        (block.directs index).1 := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token.1
        (block.directs index).1).2
    rw [htokenDirect]
    exact canonicalStableRawStateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno (block.directs index).1
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno token.1
        source.1 (block.directs index).1 hsourceIncident hdirectIncident with
    heq | ⟨u, htarget, hkind, hcomponent, _⟩ |
      ⟨u, htarget, hkind, hcomponent, _⟩
  · exact False.elim (hsource index (by
      apply Subtype.ext
      exact heq))
  · exact Or.inl ⟨u, htarget, hkind, hcomponent.trans source.2⟩
  · exact Or.inr ⟨u, htarget, hkind, hcomponent.trans source.2⟩


theorem canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (state : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state) ∨
      (∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        state.1 = collision.1.1.1) ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        state.1 = direct.1 := by
  classical
  let token := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state
  by_cases hself : state.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p state.1.source
  · let self : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨state.1, state.2, hself⟩
    by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token.1
    · let exceptionalToken : CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨token, hexceptional⟩
      let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        (canonicalStableRawComponentDirectStateEquivExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component).symm
            exceptionalToken
      have hdirectToken :
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct =
            token := by
        exact congrArg Subtype.val
          ((canonicalStableRawComponentDirectStateEquivExceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component).apply_symm_apply
              exceptionalToken)
      have hselfToken :
          canonicalStableRawComponentSelfEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            token := by
        apply Subtype.ext
        rfl
      let collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
        ⟨(self, direct), hselfToken.trans hdirectToken.symm⟩
      exact Or.inr (Or.inl ⟨collision, rfl⟩)
    · let terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨token, hexceptional⟩
      exact Or.inl ⟨terminal, rfl⟩
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨state.1, state.2, hself⟩
    exact Or.inr (Or.inr ⟨direct, rfl⟩)


theorem
    CanonicalStableRawComponentRichIncidenceBlock.closureStep_stateClassification
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        (∀ i, source ≠ block.sources i) ∧
        (∃ q, canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q) ∧
        ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            terminal.1 = canonicalStableRawComponentNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
          (∃ collision : StatMech.FrontierA.crossCollision
              (canonicalStableRawComponentSelfEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component)
              (canonicalStableRawComponentDirectEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component),
            source.1 = collision.1.1.1) ∨
          ∃ direct : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            source.1 = direct.1) := by
  rcases block.closureStep with hclosed | hextended |
      ⟨source, hsource, q, hrepeat⟩
  · exact Or.inl hclosed
  · exact Or.inr (Or.inl hextended)
  · refine Or.inr (Or.inr ⟨source, hsource, ⟨q, hrepeat⟩, ?_⟩)
    exact canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct
      ends m j k l zero hloop hjk hkl hk0 p hno component source


theorem canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (size : Nat) (hsize : 0 < size)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let natural : Fin size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    directs.trans (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  have hfresh : ∀ i, terminal.1 ≠ natural i := by
    intro i
    exact canonicalStableRawComponentNonexceptionalToken_ne_direct
      ends m j k l zero hloop hjk hkl hk0 p hno component
        terminal (directs i)
  obtain ⟨tokens, haligned, hextra⟩ :=
    finiteEmbedding_snoc size natural terminal.1 hfresh
  refine ⟨⟨size, hsize, directs, tokens, haligned, ?_⟩⟩
  rw [hextra]
  exact terminal.2


theorem CanonicalStableRawComponentRichStrictBlock.extendDirect
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfresh : ∀ q,
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct ≠
        block.tokens q) :
    ∃ extended : CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      extended.size = block.size + 1 := by
  let natural := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component direct
  have hdirectFresh : ∀ i, direct ≠ block.directs i := by
    intro i heq
    apply hfresh i.castSucc
    exact (congrArg
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component) heq).trans
          (block.aligned i).symm
  obtain ⟨extendedDirects, hdirectPrefix, hdirectLast⟩ :=
    finiteEmbedding_snoc block.size block.directs direct hdirectFresh
  have hnaturalFresh : ∀ i, natural ≠ block.tokenPrefix i := by
    intro i
    exact hfresh i.castSucc
  obtain ⟨balancedTokens, hbalancedPrefix, hbalancedLast⟩ :=
    finiteEmbedding_snoc block.size block.tokenPrefix natural hnaturalFresh
  let oldExtra := block.tokens (Fin.last block.size)
  have hextraFresh : ∀ q, oldExtra ≠ balancedTokens q := by
    intro q
    refine Fin.lastCases ?_ (fun i => ?_) q
    · rw [hbalancedLast]
      exact (hfresh (Fin.last block.size)).symm
    · rw [hbalancedPrefix]
      intro heq
      exact Fin.castSucc_ne_last i (block.tokens.injective heq.symm)
  obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
    finiteEmbedding_snoc (block.size + 1) balancedTokens oldExtra hextraFresh
  refine ⟨⟨block.size + 1, by omega, extendedDirects, extendedTokens, ?_, ?_⟩,
    rfl⟩
  · intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · calc
        extendedTokens (Fin.last block.size).castSucc =
            balancedTokens (Fin.last block.size) :=
          htokenPrefix (Fin.last block.size)
        _ = natural := hbalancedLast
        _ = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct := rfl
        _ = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (extendedDirects (Fin.last block.size)) :=
          congrArg _ hdirectLast.symm
    · calc
        extendedTokens q.castSucc.castSucc = balancedTokens q.castSucc :=
          htokenPrefix q.castSucc
        _ = block.tokenPrefix q := hbalancedPrefix q
        _ = block.tokens q.castSucc := rfl
        _ = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.directs q) := block.aligned q
        _ = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (extendedDirects q.castSucc) :=
          congrArg _ (hdirectPrefix q).symm
  · rw [htokenLast]
    exact block.extra_nonexceptional


theorem
    CanonicalStableRawComponentRichStrictBlock.extendDirect_of_freshSource
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sourceBlock i)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstate : source.1 = direct.1) :
    ∃ extended : CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      extended.size = block.size + 1 := by
  have hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 := by
    change CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1)
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg direct.2.2]
    exact canonicalStableRawDirectLeftToken_isExceptional
      ends m j k l zero hloop hjk hkl hk0 p direct.1 direct.2.2
  obtain ⟨extended, hsize⟩ := block.extendDirect direct (by
    intro q
    refine Fin.lastCases ?_ (fun i => ?_) q
    · intro heq
      apply block.extra_nonexceptional
      rw [← heq]
      exact hexceptional
    · intro heq
      have hdirectEq : direct = block.directs i := by
        apply (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component).injective
        exact heq.trans (block.aligned i)
      apply hsource i
      apply Subtype.ext
      exact hstate.trans (congrArg
        (fun state : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component => state.1)
            hdirectEq))
  exact ⟨extended, hsize⟩


theorem exists_canonicalStableRawComponent_closedRichStrictBlock_of_extension
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hextend : ∀ block : CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ¬ block.IsClosed ->
        ∃ extended : CanonicalStableRawComponentRichStrictBlock
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          extended.size = block.size + 1) :
    ∃ block : CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      block.IsClosed := by
  apply exists_closedBlock_of_strictExtension
    (Nat.card (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (fun block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component => block.size)
    CanonicalStableRawComponentRichStrictBlock.IsClosed
  · intro block
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      block.directs block.directs.injective
  · exact hextend
  · exact start


theorem CanonicalStableRawComponentRichStrictBlock.closureStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      (∃ extended : CanonicalStableRawComponentRichStrictBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 = canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          source.1 = collision.1.1.1 := by
  rcases block.closed_or_crossing with hclosed |
      ⟨source, _token, _hincident, hsource, _index, _htoken⟩
  · exact Or.inl hclosed
  · rcases canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component source with
      ⟨terminal, _hterminal⟩ | ⟨collision, hself⟩ | ⟨direct, hdirect⟩
    · exact Or.inr (Or.inr (Or.inl ⟨source, terminal, _hterminal⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨source, collision, hself⟩))
    · exact Or.inr (Or.inl
        (block.extendDirect_of_freshSource source hsource direct hdirect))


theorem canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let terminalEmbedding : Fin 1 ↪
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨fun _ => terminal, fun x y _ => Subsingleton.elim x y⟩
  let splitEmbedding := Function.Embedding.sumMap directs terminalEmbedding
  let sourceEmbedding : Fin (size + 1) ↪ Fin size ⊕ Fin 1 :=
    (finSumFinEquiv (m := size) (n := 1)).symm.toEmbedding
  exact ⟨(sourceEmbedding.trans splitEmbedding).trans
    (canonicalStableRawComponentDirectSumNonexceptionalEquivToken
      ends m j k l zero hloop hjk hkl hk0 p hno component).toEmbedding⟩


theorem
    exists_canonicalStableRawComponentDirect_terminal_or_strictTokenBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (available : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin (size + 1) ↪ Token) := by
  classical
  dsimp only
  rcases exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | ⟨size, hsize, hdirects, _htokens⟩
  · exact Or.inl hterminal
  · obtain ⟨directs⟩ := hdirects
    exact Or.inr ⟨size, hsize, ⟨directs⟩,
      canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          size directs available⟩


theorem exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (available : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let step : Direct -> Direct ⊕
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    canonicalStableRawComponentDirectForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := partialForestAdvance step
  rcases exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | ⟨size, hsize, hdirects, _htokens⟩
  · let P := fun n : Nat => ∃ terminal,
        step (advance^[n] start) = Sum.inr terminal
    have hP : ∃ n, P n := by
      obtain ⟨n, _hn, terminal, hterminal⟩ := hterminal
      refine ⟨n, terminal, ?_⟩
      simpa only [step, advance,
        canonicalStableRawComponentDirectForestAdvance,
        canonicalStableRawComponentDirectForestStep] using hterminal
    let first := Nat.find hP
    obtain ⟨terminal, hfirstTerminal⟩ := Nat.find_spec hP
    have hfirst : ∀ n < first, ∀ other,
        step (advance^[n] start) ≠ Sum.inr other := by
      intro n hn other hother
      have hle := Nat.find_min' hP ⟨other, hother⟩
      exact (Nat.not_le_of_lt hn) hle
    have horbitInjective : Function.Injective fun i : Fin (first + 1) =>
        advance^[i.1] start :=
      partialForest_iterate_injective_through_first_terminal
        step start first ⟨terminal, hfirstTerminal⟩ hfirst
    let directs : Fin (first + 1) ↪ Direct :=
      ⟨fun i => advance^[i.1] start, horbitInjective⟩
    refine ⟨first + 1, by omega, ⟨directs⟩, ?_⟩
    exact canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (first + 1) directs terminal
  · obtain ⟨directs⟩ := hdirects
    exact ⟨size, hsize, ⟨directs⟩,
      canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          size directs available⟩


theorem exists_canonicalStableRawComponentDirect_richStrictBlock_of_available
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (available : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let step : Direct -> Direct ⊕
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    canonicalStableRawComponentDirectForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := partialForestAdvance step
  rcases exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | ⟨size, hsize, hdirects, _htokens⟩
  · let P := fun n : Nat => ∃ terminal,
        step (advance^[n] start) = Sum.inr terminal
    have hP : ∃ n, P n := by
      obtain ⟨n, _hn, terminal, hterminal⟩ := hterminal
      refine ⟨n, terminal, ?_⟩
      simpa only [step, advance,
        canonicalStableRawComponentDirectForestAdvance,
        canonicalStableRawComponentDirectForestStep] using hterminal
    let first := Nat.find hP
    obtain ⟨terminal, hfirstTerminal⟩ := Nat.find_spec hP
    have hfirst : ∀ n < first, ∀ other,
        step (advance^[n] start) ≠ Sum.inr other := by
      intro n hn other hother
      have hle := Nat.find_min' hP ⟨other, hother⟩
      exact (Nat.not_le_of_lt hn) hle
    have horbitInjective : Function.Injective fun i : Fin (first + 1) =>
        advance^[i.1] start :=
      partialForest_iterate_injective_through_first_terminal
        step start first ⟨terminal, hfirstTerminal⟩ hfirst
    let directs : Fin (first + 1) ↪ Direct :=
      ⟨fun i => advance^[i.1] start, horbitInjective⟩
    exact canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (first + 1) (by omega) directs terminal
  · obtain ⟨directs⟩ := hdirects
    exact canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component
        size hsize directs available


theorem
    exists_canonicalStableRawComponentDirect_terminal_or_sourceStrictBlock_or_lowerRankEntry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        ∃ directs : Fin size ↪ Direct,
          Nonempty (Fin (size + 1) ↪ Token) ∨
            ∃ i,
              anchor.1.2.1.target = (directs i).1.target ∧
              canonicalStableRawSourceRank ends m j k l zero p
                  anchor.1.2.1.source <
                canonicalStableRawSourceRank ends m j k l zero p
                  (directs i).1.source ∧
              ∀ old : StatMech.FrontierA.crossCollision
                  (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component)
                  (canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component),
                directs i ≠ old.1.2 := by
  classical
  dsimp only
  rcases exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | ⟨size, hsize, ⟨directs⟩, _htokens⟩
  · exact Or.inl hterminal
  · right
    refine ⟨size, hsize, directs, ?_⟩
    exact canonicalStableRawComponentSourceCompanion_strictBlock_or_lowerRankEntry
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
        directs


theorem
    canonicalStableRawComponentSecondAlternatePreferredSelfOutput_orbitDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hpreferredSelf :
      (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    (exists self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inr terminal) ∨
      (exists self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inl direct ∧
          canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
            canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨
      ∃ start : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        start.1.target = canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1 ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1) ∧
        (let Direct := CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let Token := CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let advance := canonicalStableRawComponentDirectForestAdvance
            ends m j k l zero hloop hjk hkl hk0 p hno component
         (∃ n ≤ Nat.card Direct,
            ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
                Sum.inr terminal) ∨
           ∃ size : Nat, 0 < size ∧
             ∃ directs : Fin size ↪ Direct,
               Nonempty (Fin (size + 1) ↪ Token) ∨
                 ∃ i,
                   anchor.1.2.1.target = (directs i).1.target ∧
                   canonicalStableRawSourceRank ends m j k l zero p
                       anchor.1.2.1.source <
                     canonicalStableRawSourceRank ends m j k l zero p
                       (directs i).1.source ∧
                   ∀ old : StatMech.FrontierA.crossCollision
                       (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                         ends m j k l zero hloop hjk hkl hk0 p hno component)
                       (canonicalStableRawComponentDirectEmbedding
                         ends m j k l zero hloop hjk hkl hk0 p hno component),
                     directs i ≠ old.1.2) := by
  rcases canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
        hpreferredSelf with
    hterminal | hrank | ⟨start, htarget, hkind, _⟩
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hrank)
  · exact Or.inr (Or.inr ⟨start, htarget, hkind,
      exists_canonicalStableRawComponentDirect_terminal_or_sourceStrictBlock_or_lowerRankEntry
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor start⟩)


theorem
    canonicalStableRawComponentSecondAlternatePreferredSelfOutput_strictDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hpreferredSelf :
      (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    (exists self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inr terminal) ∨
      (exists self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inl direct ∧
          canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
            canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨
      ∃ start : CanonicalStableRawComponentPreferredDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        start.1.1.target = canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1.1 ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1.1) ∧
        (let Preferred := CanonicalStableRawComponentPreferredDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let Direct := CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let Token := CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let step := canonicalStableRawComponentPreferredDirectStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
         let advance := partialForestAdvance step
         (∃ n ≤ Nat.card Preferred,
            ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              step (advance^[n] start) = Sum.inr terminal) ∨
           ∃ size : Nat, 0 < size ∧
             Nonempty (Fin size ↪ Direct) ∧
             Nonempty (Fin (size + 1) ↪ Token)) := by
  rcases canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
        hpreferredSelf with
    hterminal | hrank | ⟨start, htarget, hkind, _⟩
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hrank)
  · have hstartPreferred : start.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p start.1.target,
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p start.1.target⟩ := by
      rw [htarget]
      exact hpreferredSelf
    let preferredStart : CanonicalStableRawComponentPreferredDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨start, hstartPreferred⟩
    exact Or.inr (Or.inr ⟨preferredStart, htarget, hkind,
      exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor
          preferredStart⟩)


theorem
    exists_canonicalStableRawComponentResidualLower_terminal_or_strictTokenBlock_of_freeFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (residual : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hfree : (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠
      canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let lower : Direct := residual.1.1.1.2
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] lower).1, (advance^[n] lower).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin (size + 1) ↪ Token) := by
  classical
  dsimp only
  obtain ⟨available, _havailableTarget⟩ :=
    exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor hfree
  exact exists_canonicalStableRawComponentDirect_terminal_or_strictTokenBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component
      residual.1.1.1.2 available


theorem exists_canonicalStableRawComponentResidualCollision_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nonempty (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  by_contra hnone
  have hdisjoint : ∀ collision direct,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
    intro collision direct heq
    exact hnone ⟨⟨(collision, direct), heq⟩⟩
  obtain ⟨embedding⟩ :=
    canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint
      ends m j k l zero hloop hjk hkl hk0 p hno component hdisjoint
  exact (Nat.not_lt_of_ge
    (Fintype.card_le_of_injective embedding embedding.injective)) hdeficit


theorem
    exists_canonicalStableRawComponentResidualLower_fresh_or_rightCollision_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      collision.1.1.1.2.1.target = collision.1.2.1.target ∧
      canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.2.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source ∧
      (let lower := collision.1.1.1.2
       (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨lower.1, lower.2.1⟩ = Sum.inr terminal ∧
          ∀ direct : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            terminal.1 ≠ canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨
        ∃ continuation : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨lower.1, lower.2.1⟩ = Sum.inl continuation ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                continuation =
            canonicalStableRawComponentSuccessorToken
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨lower.1, lower.2.1⟩) := by
  obtain ⟨collision⟩ :=
    exists_canonicalStableRawComponentResidualCollision_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  exact ⟨collision, hranked.1, hranked.2,
    canonicalStableRawComponentResidualLower_fresh_or_rightCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component collision⟩


theorem exists_canonicalStableRawComponent_minRankResidualCollision_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∀ other : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceSourceCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawSourceRank ends m j k l zero p
            collision.1.2.1.source ≤
          canonicalStableRawSourceRank ends m j k l zero p
            other.1.2.1.source := by
  classical
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Residual := StatMech.FrontierA.crossCollision sourceMap directMap
  let rank := fun collision : Residual =>
    canonicalStableRawSourceRank ends m j k l zero p
      collision.1.2.1.source
  letI : Fintype Residual := Fintype.ofInjective
    (fun collision => collision.1.2)
    (StatMech.FrontierA.crossCollision_snd_injective sourceMap directMap)
  obtain ⟨collision⟩ :=
    exists_canonicalStableRawComponentResidualCollision_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have huniv : (Finset.univ : Finset Residual).Nonempty :=
    ⟨collision, Finset.mem_univ collision⟩
  have hranks : (Finset.univ.image rank).Nonempty := huniv.image rank
  let minimum := (Finset.univ.image rank).min' hranks
  have hminimum : minimum ∈ Finset.univ.image rank := Finset.min'_mem _ _
  obtain ⟨chosen, _, hchosen⟩ := Finset.mem_image.mp hminimum
  refine ⟨chosen, ?_⟩
  intro other
  change rank chosen ≤ rank other
  rw [hchosen]
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨other, Finset.mem_univ other, rfl⟩)


end StatMech.GrahamGHS.FourColor
