/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part37
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

theorem canonicalStableRawComponentResidualDirectPair_card_le
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))) :
    2 * A.card ≤ Nat.card (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let embedding := canonicalStableRawComponentResidualDirectPairEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component A
  letI : Fintype (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective embedding embedding.injective
  simpa only [Fintype.card_sum, Fintype.card_coe,
    Nat.card_eq_fintype_card, two_mul] using hcard


theorem
    exists_canonicalStableRawComponentResidualOrbitDischarge_of_deficit
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
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let rank := fun direct : Direct =>
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      collision.1.1.1.2.1.target = collision.1.2.1.target ∧
      rank collision.1.1.1.2 < rank collision.1.2 ∧
      ((∃ n ≤ Nat.card Direct,
          ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  ⟨(advance^[n] collision.1.2).1,
                    (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨
        (∃ n < Nat.card Direct, ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[n] collision.1.2).1,
                  (advance^[n] collision.1.2).2.1⟩ = Sum.inl continuation ∧
            rank continuation < rank (advance^[n] collision.1.2)) ∨
        ∃ size : Nat, 0 < size ∧
          Nonempty (Fin size ↪ Direct) ∧
          Nonempty (Fin size ↪ Token)) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  obtain ⟨collision⟩ :=
    exists_canonicalStableRawComponentResidualCollision_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  refine ⟨collision, hranked.1, hranked.2, ?_⟩
  rcases
      exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.2 with
    hterminal | hdrop | hpair | hcycle
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hdrop)
  · exact Or.inr (Or.inr ⟨2, by omega, hpair.1, hpair.2⟩)
  · dsimp only at hcycle
    obtain ⟨startIndex, stopIndex, first, stop, _hlt, _hbound,
      _hrepeat, _hallNext, hfirstStop, _hstopLength, _hstate,
      _hdistinct, _howners, hdirects, htokens⟩ := hcycle
    exact Or.inr (Or.inr
      ⟨stop - first, by omega, hdirects, htokens⟩)


theorem
    exists_canonicalStableRawComponentResidual_terminal_or_balancedBlock_of_deficit
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
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
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
      ((∃ n ≤ Nat.card Direct,
          ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  ⟨(advance^[n] collision.1.2).1,
                    (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨
        ∃ size : Nat, 0 < size ∧
          Nonempty (Fin size ↪ Direct) ∧
          Nonempty (Fin size ↪ Token)) := by
  classical
  dsimp only
  obtain ⟨collision⟩ :=
    exists_canonicalStableRawComponentResidualCollision_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  refine ⟨collision, hranked.1, hranked.2, ?_⟩
  exact exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2


theorem
    exists_canonicalStableRawComponent_terminalFresh_or_reducedDeficit_of_deficit
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
    let Self := CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
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
      ((∃ n ≤ Nat.card Direct,
          ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  ⟨(advance^[n] collision.1.2).1,
                    (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal ∧
            ∀ direct : Direct,
              terminal.1 ≠ canonicalStableRawComponentDirectEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨
        ∃ size : Nat, 0 < size ∧
          Nonempty (Fin size ↪ Direct) ∧
          Nonempty (Fin size ↪ Token) ∧
          Nat.card Token - size <
            Nat.card Self + (Nat.card Direct - size)) := by
  classical
  dsimp only
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let State := CanonicalStableRawComponentState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  have hstate : Nat.card State = Nat.card Self + Nat.card Direct := by
    let split : State → Self ⊕ Direct := fun state =>
      if hself : state.1.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p state.1.source then
        Sum.inl ⟨state.1, state.2, hself⟩
      else
        Sum.inr ⟨state.1, state.2, hself⟩
    let recover : Self ⊕ Direct → State
      | Sum.inl state => ⟨state.1, state.2.1⟩
      | Sum.inr state => ⟨state.1, state.2.1⟩
    let partition : State ≃ Self ⊕ Direct := by
      refine ⟨split, recover, ?_, ?_⟩
      · intro state
        by_cases hself : state.1.target.1 = canonicalStableRawSelfBase
            ends m j k l zero hloop hjk hkl hk0 p state.1.source
        · simp [split, recover, hself]
        · simp [split, recover, hself]
      · intro state
        cases state with
        | inl state => simp [split, recover, state.2.2]
        | inr state => simp [split, recover, state.2.2]
    simpa only [Nat.card_sum] using Nat.card_congr partition
  have hdeficitNat : Nat.card Token < Nat.card Self + Nat.card Direct := by
    have hraw : Nat.card Token < Nat.card State := by
      simpa only [Nat.card_eq_fintype_card] using hdeficit
    omega
  obtain ⟨collision, htarget, hrank, horbit⟩ :=
    exists_canonicalStableRawComponentResidual_terminal_or_balancedBlock_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  refine ⟨collision, htarget, hrank, ?_⟩
  rcases horbit with hterminal | hblock
  · left
    obtain ⟨n, hn, terminal, hstep⟩ := hterminal
    exact ⟨n, hn, terminal, hstep, fun direct =>
      canonicalStableRawComponentNonexceptionalToken_ne_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component
          terminal direct⟩
  · right
    obtain ⟨size, hsize, hdirects, htokens⟩ := hblock
    refine ⟨size, hsize, hdirects, htokens, ?_⟩
    exact strictDeficit_sub_balancedEmbeddings size hdeficitNat
      hdirects htokens


theorem canonicalStableRawComponent_minResidual_terminal_or_balancedBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hminimal : ∀ other : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source ≤
        canonicalStableRawSourceRank ends m j k l zero p
          other.1.2.1.source)
    (horbitBound : ∀ n,
      canonicalStableRawSourceRank ends m j k l zero p
          ((canonicalStableRawComponentDirectForestAdvance
            ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              collision.1.2).1.source ≤
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source)
    (hresidual : ∀ n continuation,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨((canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                collision.1.2).1,
              ((canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                collision.1.2).2.1⟩ = Sum.inl continuation ->
      ∃ other : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceSourceCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        other.1.2 = continuation) :
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
              ⟨(advance^[n] collision.1.2).1,
                (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin size ↪ Token) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  rcases
      exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.2 with
    hterminal | hdrop | hpair | hcycle
  · exact Or.inl hterminal
  · obtain ⟨n, _hn, continuation, hstep, hrank⟩ := hdrop
    obtain ⟨other, hother⟩ := hresidual n continuation hstep
    have hmin : rank collision.1.2 ≤ rank continuation := by
      change canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source ≤
        canonicalStableRawSourceRank ends m j k l zero p
          continuation.1.source
      rw [← hother]
      exact hminimal other
    have hbound : rank (advance^[n] collision.1.2) ≤
        rank collision.1.2 := by
      exact horbitBound n
    have hnotDrop : ¬ rank continuation <
        rank (advance^[n] collision.1.2) :=
      Nat.not_lt_of_ge (hbound.trans hmin)
    exact False.elim (hnotDrop hrank)
  · exact Or.inr ⟨2, by omega, hpair.1, hpair.2⟩
  · dsimp only at hcycle
    obtain ⟨startIndex, stopIndex, first, stop, _hlt, _hcard,
      _hrepeat, _hallNext, hfirstStop, _hstopLength, _hstate,
      _hdistinct, _howners, hdirects, htokens⟩ := hcycle
    exact Or.inr ⟨stop - first, by omega, hdirects, htokens⟩


end StatMech.GrahamGHS.FourColor
