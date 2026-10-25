/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part14
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

theorem exists_partialForest_terminal_or_cycle
    {A B : Type*} [Fintype A] (step : A -> A ⊕ B) (start : A) :
    (∃ n ≤ Fintype.card A, ∃ terminal,
      step ((partialForestAdvance step)^[n] start) = Sum.inr terminal) ∨
      ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧
        ((partialForestAdvance step)^[i] start) =
          ((partialForestAdvance step)^[j] start) ∧
        ∀ n < j, ∃ next,
          step ((partialForestAdvance step)^[n] start) = Sum.inl next := by
  classical
  by_cases hterminal : ∃ n ≤ Fintype.card A, ∃ terminal,
      step ((partialForestAdvance step)^[n] start) = Sum.inr terminal
  · exact Or.inl hterminal
  · right
    let orbit : Fin (Fintype.card A + 1) -> A := fun n =>
      (partialForestAdvance step)^[n.1] start
    have hnotInjective : ¬ Function.Injective orbit := by
      intro hinjective
      have hcard := Fintype.card_le_of_injective orbit hinjective
      simp only [Fintype.card_fin] at hcard
      omega
    obtain ⟨u, v, horbit, huv⟩ := Function.not_injective_iff.mp hnotInjective
    obtain ⟨i, j, hij, heq, hj⟩ :
        ∃ i j : Nat, i < j ∧
          ((partialForestAdvance step)^[i] start) =
            ((partialForestAdvance step)^[j] start) ∧
          j ≤ Fintype.card A := by
      rcases lt_or_gt_of_ne huv with huv' | hvu'
      · exact ⟨u.1, v.1, huv', horbit, Nat.le_of_lt_succ v.2⟩
      · exact ⟨v.1, u.1, hvu', horbit.symm, Nat.le_of_lt_succ u.2⟩
    refine ⟨i, j, hij, hj, heq, ?_⟩
    intro n hn
    cases hstep : step ((partialForestAdvance step)^[n] start) with
    | inl next => exact ⟨next, rfl⟩
    | inr terminal =>
        exact False.elim (hterminal ⟨n, hn.le.trans hj, terminal, hstep⟩)


theorem exists_function_iterate_repeat
    {A : Type*} [Fintype A] (next : A -> A) (start : A) :
    ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧
      next^[i] start = next^[j] start := by
  let step : A -> A ⊕ Empty := fun state => Sum.inl (next state)
  have hadvance : partialForestAdvance step = next := by
    funext state
    rfl
  rcases exists_partialForest_terminal_or_cycle step start with
    hterminal | ⟨i, j, hij, hj, hrepeat, _hsteps⟩
  · obtain ⟨_n, _hn, terminal, _hterminal⟩ := hterminal
    exact terminal.elim
  · rw [hadvance] at hrepeat
    exact ⟨i, j, hij, hj, hrepeat⟩


theorem partialForest_iterate_injective_through_first_terminal
    {A B : Type*} (step : A -> A ⊕ B) (start : A) (stop : Nat)
    (hterminal : ∃ terminal,
      step ((partialForestAdvance step)^[stop] start) = Sum.inr terminal)
    (hfirst : ∀ n < stop, ∀ terminal,
      step ((partialForestAdvance step)^[n] start) ≠ Sum.inr terminal) :
    Function.Injective fun i : Fin (stop + 1) =>
      (partialForestAdvance step)^[i.1] start := by
  intro x y hxy
  have noRepeat (a b : Fin (stop + 1)) (hab : a.1 < b.1)
      (heq : (partialForestAdvance step)^[a.1] start =
        (partialForestAdvance step)^[b.1] start) : False := by
    obtain ⟨terminal, hstopTerminal⟩ := hterminal
    let shift := stop - b.1
    have hshift : a.1 + shift < stop := by
      dsimp only [shift]
      omega
    have hfuture :
        (partialForestAdvance step)^[a.1 + shift] start =
          (partialForestAdvance step)^[b.1 + shift] start := by
      let advance := partialForestAdvance step
      calc
        advance^[a.1 + shift] start =
            advance^[shift + a.1] start := by rw [Nat.add_comm a.1 shift]
        _ = advance^[shift] (advance^[a.1] start) :=
          Function.iterate_add_apply advance shift a.1 start
        _ = advance^[shift] (advance^[b.1] start) := congrArg _ heq
        _ = advance^[shift + b.1] start :=
          (Function.iterate_add_apply advance shift b.1 start).symm
        _ = advance^[b.1 + shift] start := by rw [Nat.add_comm b.1 shift]
    have hbStop : b.1 + shift = stop := by
      dsimp only [shift]
      omega
    apply hfirst (a.1 + shift) hshift terminal
    rw [hfuture, hbStop]
    exact hstopTerminal
  apply Fin.ext
  by_contra hval
  rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
  · exact False.elim (noRepeat x y hxyVal hxy)
  · exact False.elim (noRepeat y x hyxVal hxy.symm)


theorem exists_partialForest_terminal_or_rankDrop_or_maxRankCycle
    {A B : Type*} [Fintype A] (step : A -> A ⊕ B) (rank : A -> Nat)
    (start : A) (hmax : ∀ a, rank a ≤ rank start) :
    (∃ n ≤ Fintype.card A, ∃ terminal,
      step ((partialForestAdvance step)^[n] start) = Sum.inr terminal) ∨
      (∃ n < Fintype.card A, ∃ next,
        step ((partialForestAdvance step)^[n] start) = Sum.inl next ∧
          rank next < rank start) ∨
      ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧
        ((partialForestAdvance step)^[i] start) =
          ((partialForestAdvance step)^[j] start) ∧
        ∀ n < j, ∃ next,
          step ((partialForestAdvance step)^[n] start) = Sum.inl next ∧
            rank next = rank start := by
  classical
  rcases exists_partialForest_terminal_or_cycle step start with
    hterminal | ⟨i, j, hij, hj, hrepeat, hsteps⟩
  · exact Or.inl hterminal
  · right
    by_cases hdrop : ∃ n < j, ∃ next,
        step ((partialForestAdvance step)^[n] start) = Sum.inl next ∧
          rank next < rank start
    · left
      obtain ⟨n, hn, next, hstep, hrank⟩ := hdrop
      exact ⟨n, by omega, next, hstep, hrank⟩
    · right
      refine ⟨i, j, hij, hj, hrepeat, ?_⟩
      intro n hn
      obtain ⟨next, hstep⟩ := hsteps n hn
      refine ⟨next, hstep, ?_⟩
      have hnotlt : ¬ rank next < rank start := by
        intro hrank
        exact hdrop ⟨n, hn, next, hstep, hrank⟩
      have hle := hmax next
      omega


theorem map_iterate_eq_of_step_until
    {A B : Type*} (f : A -> A) (g : B -> B) (project : A -> B)
    (start : A) (length : Nat)
    (hstep : ∀ n < length,
      project (f ((f^[n]) start)) = g (project ((f^[n]) start))) :
    project ((f^[length]) start) = (g^[length]) (project start) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [Function.iterate_succ_apply']
      calc
        project (f ((f^[length]) start)) =
            g (project ((f^[length]) start)) := hstep length (by omega)
        _ = g ((g^[length]) (project start)) := congrArg g (ih (by
          intro n hn
          exact hstep n (by omega)))
        _ = (g^[length + 1]) (project start) := by
          rw [Function.iterate_succ_apply']


theorem exists_minimal_iterateKey_repeat_of_closedOrbit
    {A K : Type*} (f : A -> A) (key : A -> K) (start : A)
    (length : Nat) (hlength : 0 < length)
    (hrepeat : (f^[length] start) = start) :
    ∃ first stop : Nat, first < stop ∧ stop ≤ length ∧
      key (f^[first] start) = key (f^[stop] start) ∧
      ∀ a b : Nat, a < b -> b < stop ->
        key (f^[a] start) ≠ key (f^[b] start) := by
  classical
  let orbitKey := fun n : Nat => key (f^[n] start)
  let P := fun n : Nat => ∃ i < n, orbitKey i = orbitKey n
  have hP : ∃ n, P n := by
    refine ⟨length, 0, hlength, ?_⟩
    change key start = key (f^[length] start)
    exact congrArg key hrepeat.symm
  let stop := Nat.find hP
  obtain ⟨first, hfirstStop, hkey⟩ := Nat.find_spec hP
  have hstopBound : stop ≤ length :=
    Nat.find_min' hP (by
      refine ⟨0, hlength, ?_⟩
      change key start = key (f^[length] start)
      exact congrArg key hrepeat.symm)
  refine ⟨first, stop, hfirstStop, hstopBound, hkey, ?_⟩
  intro a b hab hbStop habKey
  have hPb : P b := ⟨a, hab, habKey⟩
  have hstopLe := Nat.find_min' hP hPb
  exact (Nat.not_le_of_lt hbStop) hstopLe


theorem exists_function_cycleEmbedding
    {A : Type*} [Fintype A] (next : A -> A) (start : A) :
    ∃ size : Nat, 0 < size ∧
      ∃ cycle : Fin size ↪ A, ∃ σ : Equiv.Perm (Fin size),
        ∀ i, cycle (σ i) = next (cycle i) := by
  classical
  obtain ⟨a, b, hab, _hb, hrepeat⟩ :=
    exists_function_iterate_repeat next start
  let base := next^[a] start
  let length := b - a
  have hlength : 0 < length := by
    dsimp only [length]
    omega
  have hclosed : next^[length] base = base := by
    calc
      next^[length] base = next^[length + a] start := by
        exact (Function.iterate_add_apply next length a start).symm
      _ = next^[b] start := by congr 2 <;> omega
      _ = next^[a] start := hrepeat.symm
      _ = base := rfl
  obtain ⟨first, stop, hfirstStop, _hstopLength, hstate, hdistinct⟩ :=
    exists_minimal_iterateKey_repeat_of_closedOrbit
      next id base length hlength hclosed
  have hcyclePos : 0 < stop - first := by omega
  obtain ⟨cycleN, hcycle⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hcyclePos)
  let cycleState : Fin (cycleN + 1) -> A := fun x =>
    next^[first + x.1] base
  have hcycleStateInjective : Function.Injective cycleState := by
    intro x y hxy
    apply Fin.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
    · exact (hdistinct (first + x.1) (first + y.1) (by omega)
          (by omega)) hxy
    · exact (hdistinct (first + y.1) (first + x.1) (by omega)
          (by omega)) hxy.symm
  let cycle : Fin (cycleN + 1) ↪ A :=
    ⟨cycleState, hcycleStateInjective⟩
  let σ : Equiv.Perm (Fin (cycleN + 1)) := finRotate (cycleN + 1)
  have hcycleStep : ∀ x, cycle (σ x) = next (cycle x) := by
    intro x
    by_cases hx : x = Fin.last cycleN
    · subst x
      simp only [cycle, cycleState, σ, finRotate_last,
        Fin.val_zero, Fin.val_last]
      calc
        next^[first] base = next^[stop] base := by
          simpa only [id_eq] using hstate
        _ = next^[Nat.succ (first + cycleN)] base := by
          congr 2 <;> omega
        _ = next (next^[first + cycleN] base) :=
          Function.iterate_succ_apply' next (first + cycleN) base
    · have hrotate : (σ x).1 = x.1 + 1 :=
        coe_finRotate_of_ne_last hx
      change next^[first + (σ x).1] base =
        next (next^[first + x.1] base)
      rw [hrotate]
      convert Function.iterate_succ_apply' next (first + x.1) base using 1 <;>
        omega
  exact ⟨cycleN + 1, by omega, cycle, σ, hcycleStep⟩


theorem canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)) :
    (canonicalStableRawExceptionalEdgeOfLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawDirectAlternateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)
          hexceptional).target =
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
  classical
  apply Subtype.ext
  change (canonicalStableRawDirectAlternateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s hdirect).2.1 =
    (canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s).target.1
  rw [canonicalStableRawDirectAlternateLeftToken]
  dsimp only
  by_cases hsourceSelf :
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target.1 =
        canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source
  · rw [dif_pos hsourceSelf]
    by_cases hownerSelf : s.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p s.target,
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p s.target⟩
    · rw [dif_pos hownerSelf]
    · rw [dif_neg hownerSelf]
      exfalso
      apply hexceptional
      unfold canonicalStableRawLeftTokenTarget
      rw [canonicalStableRawDirectAlternateLeftToken]
      dsimp only
      rw [dif_pos hsourceSelf, dif_neg hownerSelf]
  · rw [dif_neg hsourceSelf]


theorem canonicalStableRawDirectAlternateExceptionalEdge_next_or_sibling
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)) :
    let recovered := canonicalStableRawExceptionalEdgeOfLeftToken
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)
        hexceptional
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    recovered = next ∨
      (recovered.source ≠ next.source ∧ recovered.target = next.target) := by
  dsimp only
  have htarget :=
    canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next
      ends m j k l zero hloop hjk hkl hk0 p hno s hdirect hexceptional
  rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
      (canonicalStableRawExceptionalEdgeOfLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawDirectAlternateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)
          hexceptional)
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s) htarget with
    hsource | heq
  · exact Or.inr ⟨hsource, htarget⟩
  · exact Or.inl heq


theorem canonicalStableRawReferenceOwnerLeftToken_rank_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawSourceRank ends m j k l zero p
        (canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hself).1 <
      canonicalStableRawSourceRank ends m j k l zero p s.source := by
  change canonicalStableRawSourceRank ends m j k l zero p
      (canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s) <
    canonicalStableRawSourceRank ends m j k l zero p s.source
  exact canonicalStableRawPreferredRightBase_rank_lt_of_self
    ends m j k l zero hloop hjk hkl hk0 p s.target s.source
      hself.symm s.exceptional


end StatMech.GrahamGHS.FourColor
