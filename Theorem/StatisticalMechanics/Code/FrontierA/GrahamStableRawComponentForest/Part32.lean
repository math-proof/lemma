/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part31
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

theorem
    canonicalStableRawComponentSecondAlternateFiberMinusOne_directResidual
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
    (member : ↑(canonicalStableRawComponentSecondAlternateFiberMinusOne
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor))
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (htransport : canonicalStableRawComponentSecondAlternateFiberMinusOneSourceTransport
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor member =
      Sum.inl direct) :
    ∃ residual : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      residual.1.1 = member.1 ∧ residual.1.2 = direct ∧
      residual.1.1.1.2.1.target = residual.1.2.1.target ∧
      canonicalStableRawSourceRank ends m j k l zero p
          residual.1.1.1.2.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          residual.1.2.1.source := by
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let tokenEquiv := canonicalStableRawComponentDirectSumNonexceptionalEquivToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  change tokenEquiv.symm (sourceMap member.1) = Sum.inl direct at htransport
  have htoken := congrArg tokenEquiv htransport
  rw [tokenEquiv.apply_symm_apply] at htoken
  change sourceMap member.1 = directMap direct at htoken
  let residual : StatMech.FrontierA.crossCollision sourceMap directMap :=
    ⟨(member.1, direct), htoken⟩
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component residual
  exact ⟨residual, rfl, rfl, hranked.1, hranked.2⟩


theorem canonicalStableRawComponentSecondAlternateFiber_erase_card
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
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (canonicalStableRawComponentSecondAlternateFiberMinusOne
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).card + 1 =
      (canonicalStableRawComponentSecondCollisionAlternateFiber
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).card := by
  classical
  unfold canonicalStableRawComponentSecondAlternateFiberMinusOne
  apply Finset.card_erase_add_one
  simp only [canonicalStableRawComponentSecondCollisionAlternateFiber,
    Finset.mem_filter, Finset.mem_univ, true_and]


theorem canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (size : Nat)
    (tokens : Fin size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (extra : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfresh : ∀ i, extra ≠ tokens i) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let f : Fin size ⊕ Fin 1 → CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl i => tokens i
    | Sum.inr _ => extra
  have hinjective : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (tokens.injective hxy)
        | inr y => exact False.elim (hfresh x hxy.symm)
    | inr x =>
        cases y with
        | inl y => exact False.elim (hfresh y hxy)
        | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  let block : Fin size ⊕ Fin 1 ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨f, hinjective⟩
  exact ⟨(finSumFinEquiv (m := size) (n := 1)).symm.toEmbedding.trans block⟩


theorem canonicalStableRawComponentTokenBlock_add_freshSourceCompanion
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
    (size : Nat)
    (tokens : Fin size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfresh : ∀ i,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ≠
        tokens i) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component size tokens
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor)
      hfresh


theorem
    canonicalStableRawComponentReferenceSource_fresh_from_preferredSelfCycle
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
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (σ : Equiv.Perm (Fin size))
    (hstep : ∀ i,
      (directs (σ i)).1 = canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1)
    (hpreferredSelf : ∀ i, (directs i).1.target.1 =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p (directs i).1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p (directs i).1.target⟩) :
    ∀ i,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) := by
  classical
  intro i hcollision
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let residual : StatMech.FrontierA.crossCollision sourceMap directMap :=
    ⟨(anchor, directs i), hcollision⟩
  let previous := σ.symm i
  have hpreviousStep : (directs i).1 =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
          (directs previous).1 := by
    calc
      (directs i).1 = (directs (σ previous)).1 := by simp [previous]
      _ = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            (directs previous).1 := hstep previous
  have hadvancePrevious : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno
        (directs previous).1 := by
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno
          (directs previous).1 with hadvance | hstable
    · exact hadvance
    · exfalso
      apply canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
        ends m j k l zero hloop hjk hkl hk0 p hno
          (directs previous).1 (hpreferredSelf previous) hstable
      rw [← hpreviousStep]
      exact hpreferredSelf i
  let previousOwner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p (directs previous).1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p (directs previous).1.target⟩
  have hupperSource : (directs i).1.source = previousOwner := by
    apply Subtype.ext
    calc
      (directs i).1.source.1 =
          (canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              (directs previous).1).source.1 :=
        congrArg (fun edge => edge.source.1) hpreviousStep
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p (directs previous).1.target :=
        hadvancePrevious
  have hupperSelf : canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p (directs i).1.source =
      (directs previous).1.target.1 := by
    rw [hupperSource]
    exact (hpreferredSelf previous).symm
  have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component residual
  have hbase :=
    canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq
      ends m j k l zero hloop hjk hkl hk0 p hno component residual
  have hlowerSelf : canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1.source =
      (directs previous).1.target.1 := by
    calc
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          anchor.1.2.1.source =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          (directs i).1.source := by
            simpa only [residual] using hbase.symm
      _ = (directs previous).1.target.1 := hupperSelf
  have hsourceNe : anchor.1.2.1.source ≠ (directs i).1.source := by
    intro heq
    have hbad : canonicalStableRawSourceRank ends m j k l zero p
          (directs i).1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          (directs i).1.source := by
      simpa only [residual, heq] using hranked.2
    exact (Nat.lt_irrefl _ hbad)
  have hnePreferred : anchor.1.2.1.source.1 ≠
      canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p (directs previous).1.target := by
    intro heq
    apply hsourceNe
    exact Subtype.ext (heq.trans (congrArg Subtype.val hupperSource).symm)
  have hreverse := canonicalStableRawPreferredRightBase_rank_lt_of_self
    ends m j k l zero hloop hjk hkl hk0 p (directs previous).1.target
      anchor.1.2.1.source hlowerSelf hnePreferred
  have hreverse' : canonicalStableRawSourceRank ends m j k l zero p
        (directs i).1.source <
      canonicalStableRawSourceRank ends m j k l zero p
        anchor.1.2.1.source := by
    rw [hupperSource]
    exact hreverse
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hranked.2)) hreverse'


theorem
    canonicalStableRawComponentPreferredSelfCycle_strictTokenBlock
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
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (σ : Equiv.Perm (Fin size))
    (hstep : ∀ i,
      (directs (σ i)).1 = canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1)
    (hpreferredSelf : ∀ i, (directs i).1.target.1 =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p (directs i).1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p (directs i).1.target⟩) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  exact canonicalStableRawComponentTokenBlock_add_freshSourceCompanion
    ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
      (directs.trans (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
      (canonicalStableRawComponentReferenceSource_fresh_from_preferredSelfCycle
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
          directs σ hstep hpreferredSelf)


theorem
    exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock
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
    (start : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Preferred := CanonicalStableRawComponentPreferredDirectState
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
        Nonempty (Fin (size + 1) ↪ Token) := by
  classical
  dsimp only
  let Preferred := CanonicalStableRawComponentPreferredDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let step : Preferred → Preferred ⊕
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    canonicalStableRawComponentPreferredDirectStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := partialForestAdvance step
  letI : Fintype Preferred := Fintype.ofFinite Preferred
  rcases exists_partialForest_terminal_or_cycle step start with
    hterminal | ⟨startIndex, stopIndex, hlt, hbound, hrepeat, hsteps⟩
  · left
    simpa only [Nat.card_eq_fintype_card] using hterminal
  · let base := advance^[startIndex] start
    let length := stopIndex - startIndex
    have hlength : 0 < length := by omega
    have hshift (n : Nat) : advance^[n] base =
        advance^[startIndex + n] start := by
      calc
        advance^[n] base = advance^[n + startIndex] start := by
          exact (Function.iterate_add_apply advance n startIndex start).symm
        _ = advance^[startIndex + n] start := by rw [Nat.add_comm]
    have hclosed : advance^[length] base = base := by
      calc
        advance^[length] base = advance^[startIndex + length] start := hshift length
        _ = advance^[stopIndex] start := by congr 2 <;> omega
        _ = advance^[startIndex] start := hrepeat.symm
    have hcontinuation (n : Nat) (hn : n < length) :
        ∃ next, step (advance^[n] base) = Sum.inl next := by
      obtain ⟨next, hnext⟩ := hsteps (startIndex + n) (by omega)
      refine ⟨next, ?_⟩
      rw [hshift n]
      exact hnext
    obtain ⟨first, stop, hfirstStop, hstopLength, hstate, hdistinct⟩ :=
      exists_minimal_iterateKey_repeat_of_closedOrbit
        advance id base length hlength hclosed
    have hcyclePos : 0 < stop - first := by omega
    obtain ⟨cycleN, hcycle⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hcyclePos)
    let cycleState : Fin (cycleN + 1) → Preferred := fun x =>
      advance^[first + x.1] base
    let σ : Equiv.Perm (Fin (cycleN + 1)) := finRotate (cycleN + 1)
    have hcycleStateInjective : Function.Injective cycleState := by
      intro x y hxy
      apply Fin.ext
      by_contra hval
      rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
      · exact (hdistinct (first + x.1) (first + y.1) (by omega)
          (by omega)) hxy
      · exact (hdistinct (first + y.1) (first + x.1) (by omega)
          (by omega)) hxy.symm
    let directs : Fin (cycleN + 1) ↪ Direct :=
      ⟨fun x => (cycleState x).1, fun x y hxy =>
        hcycleStateInjective (Subtype.ext hxy)⟩
    have hcycleStep : ∀ x, cycleState (σ x) =
        advance (cycleState x) := by
      intro x
      by_cases hx : x = Fin.last cycleN
      · subst x
        simp only [cycleState, σ, finRotate_last, Fin.val_zero, Fin.val_last]
        calc
          advance^[first] base = advance^[stop] base := hstate
          _ = advance^[Nat.succ (first + cycleN)] base := by
            congr 2 <;> omega
          _ = advance (advance^[first + cycleN] base) :=
            Function.iterate_succ_apply' advance (first + cycleN) base
      · have hrotate : (σ x).1 = x.1 + 1 :=
          coe_finRotate_of_ne_last hx
        simp only [cycleState]
        rw [hrotate]
        convert Function.iterate_succ_apply' advance (first + x.1) base using 1 <;>
          omega
    have hrawStep : ∀ x, (directs (σ x)).1 =
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno (directs x).1 := by
      intro x
      have hxBound : first + x.1 < length := by
        have hxCycle : x.1 < stop - first := by simpa only [hcycle] using x.2
        omega
      obtain ⟨next, hnext⟩ := hcontinuation (first + x.1) hxBound
      have hadvance :=
        canonicalStableRawComponentPreferredDirectAdvance_eq_of_step
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (cycleState x) next hnext
      calc
        (directs (σ x)).1 = (cycleState (σ x)).1.1 := rfl
        _ = (advance (cycleState x)).1.1 := congrArg
          (fun state : Preferred => state.1.1) (hcycleStep x)
        _ = next.1.1 := congrArg (fun state : Preferred => state.1.1) hadvance
        _ = canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              (cycleState x).1.1 :=
          canonicalStableRawComponentPreferredDirectStep_inl_next
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (cycleState x) next hnext
        _ = canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno (directs x).1 := rfl
    have hpreferred : ∀ x, (directs x).1.target.1 =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p (directs x).1.target,
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p (directs x).1.target⟩ := fun x =>
      (cycleState x).2
    exact Or.inr ⟨cycleN + 1, by omega, ⟨directs⟩,
      canonicalStableRawComponentPreferredSelfCycle_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor
          (cycleN + 1) directs σ hrawStep hpreferred⟩


theorem
    exists_canonicalStableRawComponentPreferredDirect_strictTokenBlock
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
    (start : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    ∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ Direct) ∧
      Nonempty (Fin (size + 1) ↪ Token) := by
  classical
  dsimp only
  let Preferred := CanonicalStableRawComponentPreferredDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let step : Preferred → Preferred ⊕
      CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
    canonicalStableRawComponentPreferredDirectStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := partialForestAdvance step
  rcases
      exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor start with
    hterminal | hstrict
  · let P := fun n : Nat => ∃ terminal,
        step (advance^[n] start) = Sum.inr terminal
    have hP : ∃ n, P n := by
      obtain ⟨n, _hn, terminal, hterminal⟩ := hterminal
      exact ⟨n, terminal, hterminal⟩
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
    let preferredOrbit : Fin (first + 1) ↪ Preferred :=
      ⟨fun i => advance^[i.1] start, horbitInjective⟩
    let directs : Fin (first + 1) ↪ Direct :=
      preferredOrbit.trans ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨first + 1, by omega, ⟨directs⟩, ?_⟩
    exact canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (first + 1)
        (directs.trans (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component))
        terminal.1 (fun i =>
          canonicalStableRawComponentNonexceptionalToken_ne_direct
            ends m j k l zero hloop hjk hkl hk0 p hno component
              terminal (directs i))
  · exact hstrict


theorem canonicalStableRawComponentDirect_strictTokenBlock_of_anchor
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
    ∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  by_cases hpreferred : start.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p start.1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p start.1.target⟩
  · let preferredStart : CanonicalStableRawComponentPreferredDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨start, hpreferred⟩
    exact exists_canonicalStableRawComponentPreferredDirect_strictTokenBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
        preferredStart
  · let raw := canonicalStableRawPreferredFreeLeftToken
        ends m j k l zero hloop hjk hkl hk0 p start.1.target hpreferred
    have hrawComponent : canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno raw = component :=
      (canonicalStableRawPreferredFreeLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno start.1 hpreferred).trans
          start.2.1
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨⟨raw, hrawComponent⟩,
        canonicalStableRawPreferredFreeLeftToken_not_exceptional
          ends m j k l zero hloop hjk hkl hk0 p start.1.target hpreferred⟩
    let directs : Fin 1 ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨fun _ => start, fun x y _ => Subsingleton.elim x y⟩
    refine ⟨1, by omega, ⟨directs⟩, ?_⟩
    exact canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component 1
        (directs.trans (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component))
        terminal.1 (fun i =>
          canonicalStableRawComponentNonexceptionalToken_ne_direct
            ends m j k l zero hloop hjk hkl hk0 p hno component
              terminal (directs i))


theorem
    exists_canonicalStableRawComponentSecondCollision_strictTokenBlock
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
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  have strictOfTerminal
      (terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    let directs : Fin 1 ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨fun _ => anchor.1.2, fun x y _ => Subsingleton.elim x y⟩
    refine ⟨1, by omega, ⟨directs⟩, ?_⟩
    exact canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component 1
        (directs.trans (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component))
        terminal.1 (fun i =>
          canonicalStableRawComponentNonexceptionalToken_ne_direct
            ends m j k l zero hloop hjk hkl hk0 p hno component
              terminal (directs i))
  rcases
      canonicalStableRawComponentSecondAlternateFiber_terminal_or_preferredSelfOutput
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor with
    ⟨terminal, _⟩ | ⟨_u, _htarget, _hkind, _hcomponent, hpreferred⟩
  · exact strictOfTerminal terminal
  · rcases
        canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor
            hpreferred with
      ⟨_self, terminal, _htarget, _hstep⟩ |
      ⟨_self, direct, _htarget, _hstep, _hrank⟩ |
      ⟨direct, _htarget, _hkind, _hpreferred⟩
    · exact strictOfTerminal terminal
    · exact canonicalStableRawComponentDirect_strictTokenBlock_of_anchor
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor direct
    · exact canonicalStableRawComponentDirect_strictTokenBlock_of_anchor
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor direct


theorem
    canonicalStableRawComponentSourceCompanion_strictBlock_or_residualCollision
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
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ residual : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceSourceCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        residual.1.1 = anchor ∧
          (∃ i, residual.1.2 = directs i) ∧
          ∀ old : StatMech.FrontierA.crossCollision
              (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component)
              (canonicalStableRawComponentDirectEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component),
            residual.1.2 ≠ old.1.2 := by
  classical
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  by_cases hfresh : ∀ i, sourceMap anchor ≠ directMap (directs i)
  · left
    exact canonicalStableRawComponentTokenBlock_add_freshSourceCompanion
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
        (directs.trans directMap) hfresh
  · right
    push Not at hfresh
    obtain ⟨i, hi⟩ := hfresh
    let residual : StatMech.FrontierA.crossCollision sourceMap directMap :=
      ⟨(anchor, directs i), hi⟩
    let unused :=
      canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
    exact ⟨residual, rfl, ⟨i, rfl⟩, (unused residual).2⟩


theorem
    canonicalStableRawComponentSourceCompanion_strictBlock_or_lowerRankEntry
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
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
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
  rcases
      canonicalStableRawComponentSourceCompanion_strictBlock_or_residualCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor size
          directs with
    hstrict | ⟨residual, hanchor, ⟨i, hi⟩, hunused⟩
  · exact Or.inl hstrict
  · right
    have hranked := canonicalStableRawComponentResidualCollision_ranked_sameTarget
      ends m j k l zero hloop hjk hkl hk0 p hno component residual
    refine ⟨i, ?_, ?_, ?_⟩
    · simpa only [hanchor, hi] using hranked.1
    · simpa only [hanchor, hi] using hranked.2
    · intro old heq
      exact hunused old (hi.trans heq)


end StatMech.GrahamGHS.FourColor
