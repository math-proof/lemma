/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part35
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

theorem CanonicalStableRawComponentRichIncidenceBlock.closed_or_crossing
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
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          (∀ i, source ≠ block.sources i) ∧
          ∃ i, token = block.tokenPrefix i := by
  exact finiteRelationTokenClosed_or_crossing
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sources block.tokenPrefix

theorem CanonicalStableRawComponentRichIncidenceBlock.reducedDeficit
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
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hclosed : block.IsClosed)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) <
      Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Fintype.card (FiniteEmbeddingComplement block.size block.tokenPrefix) <
        Fintype.card (FiniteEmbeddingComplement block.size block.sources) ∧
      ∀ source : FiniteEmbeddingComplement block.size block.sources,
        ∀ token,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token ->
            token ∉ finiteEmbeddingBlock block.size block.tokenPrefix := by
  refine ⟨finiteEmbeddingComplement_strictDeficit
      block.size block.sources block.tokenPrefix hdeficit, ?_⟩
  intro source token hincident
  exact finiteRelationComplement_tokenClosed
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sources block.tokenPrefix hclosed source token hincident

theorem exists_canonicalStableRawComponent_closedRichIncidenceBlock_of_extension
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hextend : ∀ block : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ¬ block.IsClosed ->
        ∃ extended : CanonicalStableRawComponentRichIncidenceBlock
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          extended.size = block.size + 1) :
    ∃ block : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      block.IsClosed := by
  apply exists_closedBlock_of_strictExtension
    (Nat.card (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (fun block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component => block.size)
    CanonicalStableRawComponentRichIncidenceBlock.IsClosed
  · intro block
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      block.sources block.sources.injective
  · exact hextend
  · exact start


theorem exists_canonicalStableRawComponent_sizeMaximalRichIncidenceBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ block : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∀ other : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        other.size ≤ block.size := by
  apply exists_sizeMaximalBlock
    (Nat.card (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (fun block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component => block.size)
  · intro block
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      block.sources block.sources.injective
  · exact start

theorem CanonicalStableRawComponentRichIncidenceBlock.closureStep
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
        ∃ q, canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q := by
  rcases block.closed_or_crossing with hclosed |
      ⟨source, _crossingToken, _hcrossing, hsource, _index, _htoken⟩
  · exact Or.inl hclosed
  · let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component source
    have hnaturalIncident : CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source natural := by
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p natural.1 source.1).2
      exact canonicalStableRawStateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno source.1
    by_cases hfresh : ∀ q, natural ≠ block.tokens q
    · exact Or.inr (Or.inl
        (block.extend source natural hsource hfresh hnaturalIncident))
    · right
      right
      push Not at hfresh
      exact ⟨source, hsource, hfresh⟩


theorem canonicalStableRawComponent_naturalToken_target_eq_of_direct
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.source) :
    canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source).1 =
      source.1.target := by
  classical
  change canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno source.1) =
    source.1.target
  unfold canonicalStableRawStateLeftToken
  rw [dif_neg hdirect]
  rfl


theorem canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.source)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source).1)
    (hstable : CanonicalStableRawOwnerStableOutput
      ends m j k l zero hloop hjk hkl hk0 p source.1 u) :
    u = source.1 := by
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
  · exact hstable.1
  · exact htarget.trans
      (canonicalStableRawComponent_naturalToken_target_eq_of_direct
        source hdirect)


theorem canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.source)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source).1)
    (hadvancing : CanonicalStableRawOwnerAdvancingOutput
      ends m j k l zero hloop hjk hkl hk0 p source.1 u) : False := by
  apply u.exceptional
  exact hadvancing.trans (congrArg
    (canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget.trans
      (canonicalStableRawComponent_naturalToken_target_eq_of_direct
        source hdirect)).symm)

theorem
    CanonicalStableRawComponentRichIncidenceBlock.repeatedNaturalDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i)
    (q : Fin (block.size + 1))
    (hrepeat : canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component source =
      block.tokens q) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
      (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧
          CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component source
  by_cases hlast : q = Fin.last block.size
  · subst q
    left
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨natural, by
        intro hexceptional
        apply block.extra_nonexceptional
        rw [← hrepeat]
        exact hexceptional⟩
    exact ⟨terminal, rfl⟩
  · have hlt : q < Fin.last block.size :=
      Fin.lt_last_iff_ne_last.mpr hlast
    let i : Fin block.size := ⟨q.1, by
      exact hlt⟩
    have hq : i.castSucc = q := by
      apply Fin.ext
      rfl
    rw [← hq] at hrepeat
    have hnewIncident : CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p natural.1 source.1 := by
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p natural.1 source.1).2
      exact canonicalStableRawStateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno source.1
    have holdIncident : CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p natural.1
          (block.sources i).1 := by
      have hpaired := block.paired i
      rw [← hrepeat] at hpaired
      exact hpaired
    rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
        ends m j k l zero hloop hjk hkl hk0 p hno natural.1
          source.1 (block.sources i).1 hnewIncident holdIncident with
      heq | ⟨u, htarget, hkind, hcomponent, _⟩ |
        ⟨u, htarget, hkind, hcomponent, _⟩
    · exact False.elim (hsource i (Subtype.ext heq))
    · exact Or.inr (Or.inl
        ⟨u, htarget, hkind, hcomponent.trans source.2⟩)
    · exact Or.inr (Or.inr
        ⟨u, htarget, hkind, hcomponent.trans source.2⟩)

theorem CanonicalStableRawComponentRichIncidenceBlock.closureDischarge
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
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 = canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    source).1 ∧
            CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    source).1 ∧
            CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  rcases block.closureStep with hclosed | hextended |
      ⟨source, hsource, q, hrepeat⟩
  · exact Or.inl hclosed
  · exact Or.inr (Or.inl hextended)
  · rcases block.repeatedNaturalDischarge source hsource q hrepeat with
      ⟨terminal, hterminal⟩ | ⟨u, htarget, hstable, hcomponent⟩ |
        ⟨u, htarget, hadvancing, hcomponent⟩
    · exact Or.inr (Or.inr (Or.inl ⟨source, terminal, hterminal⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨source, u, htarget, hstable, hcomponent⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨source, u, htarget, hadvancing, hcomponent⟩)))


theorem
    CanonicalStableRawComponentRichIncidenceBlock.extendBySuccessor_or_repeat
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i) :
    (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ q, canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q := by
  let successor := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component source
  have hsuccessorIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source successor :=
    canonicalStableRawComponentSuccessorToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component source
  by_cases hfresh : ∀ q, successor ≠ block.tokens q
  · exact Or.inl (block.extend source successor hsource hfresh hsuccessorIncident)
  · right
    push Not at hfresh
    exact hfresh

theorem
    CanonicalStableRawComponentRichIncidenceBlock.repeatedSuccessorDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i)
    (q : Fin (block.size + 1))
    (hrepeat : canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component source =
      block.tokens q) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 = canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨
      (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧
          CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let successor := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component source
  by_cases hlast : q = Fin.last block.size
  · subst q
    left
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨successor, by
        intro hexceptional
        apply block.extra_nonexceptional
        rw [← hrepeat]
        exact hexceptional⟩
    exact ⟨terminal, rfl⟩
  · have hlt : q < Fin.last block.size :=
      Fin.lt_last_iff_ne_last.mpr hlast
    let i : Fin block.size := ⟨q.1, hlt⟩
    have hq : i.castSucc = q := by
      apply Fin.ext
      rfl
    rw [← hq] at hrepeat
    have hnewIncident : CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p successor.1 source.1 :=
      canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    have holdIncident : CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p successor.1
          (block.sources i).1 := by
      have hpaired := block.paired i
      rw [← hrepeat] at hpaired
      exact hpaired
    rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
        ends m j k l zero hloop hjk hkl hk0 p hno successor.1
          source.1 (block.sources i).1 hnewIncident holdIncident with
      heq | ⟨u, htarget, hkind, hcomponent, _⟩ |
        ⟨u, htarget, hkind, hcomponent, _⟩
    · exact False.elim (hsource i (Subtype.ext heq))
    · exact Or.inr (Or.inl
        ⟨u, htarget, hkind, hcomponent.trans source.2⟩)
    · exact Or.inr (Or.inr
        ⟨u, htarget, hkind, hcomponent.trans source.2⟩)


end StatMech.GrahamGHS.FourColor
