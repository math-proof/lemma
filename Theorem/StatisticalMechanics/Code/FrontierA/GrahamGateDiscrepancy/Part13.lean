/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part11


namespace StatMech.FrontierA

theorem RelationPartialMatching.HoleState.card_naturalSupport_lt_move_of_ne
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (hne : natural state.hole ≠
      natural (state.move natural hnatural).hole) :
    (state.naturalSupport natural).card <
      ((state.move natural hnatural).naturalSupport natural).card := by
  classical
  let moved := state.move natural hnatural
  have hcurrentNot : state.hole ∉ state.naturalSupport natural := by
    intro hmem
    have hmatch : state.matching.toFun state.hole =
        some (natural state.hole) := by
      simpa only [RelationPartialMatching.HoleState.naturalSupport,
        Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    exact state.hole_unmatched
      ((RelationPartialMatching.mem_support_iff state.matching state.hole).2
        ⟨natural state.hole, hmatch⟩)
  have hcurrentMem : state.hole ∈ moved.naturalSupport natural := by
    simp only [RelationPartialMatching.HoleState.naturalSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact state.move_matching_apply_hole natural hnatural
  have hsubset : state.naturalSupport natural ⊆
      moved.naturalSupport natural := by
    intro x hx
    have hxMatch : state.matching.toFun x = some (natural x) := by
      simpa only [RelationPartialMatching.HoleState.naturalSupport,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hxCurrent : x ≠ state.hole := by
      intro h
      exact hcurrentNot (h ▸ hx)
    have hxNext : x ≠ moved.hole := by
      intro h
      have hoccupied := state.matching_apply_move_hole natural hnatural
      rw [← h] at hoccupied
      have htargets : natural x = natural state.hole := by
        exact Option.some.inj (hxMatch.symm.trans hoccupied)
      exact hne (htargets.symm.trans (congrArg natural h))
    simp only [RelationPartialMatching.HoleState.naturalSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact (state.move_matching_apply_of_ne natural hnatural x
      hxCurrent hxNext).trans hxMatch
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_subset_ne).2
  refine ⟨hsubset, ?_⟩
  intro heq
  exact hcurrentNot (heq ▸ hcurrentMem)


theorem RelationPartialMatching.exists_maximalNatural_holeState_collision
    {A B : Type*} [Fintype A] [Fintype B] (r : A -> B -> Prop)
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (hcard : Fintype.card B < Fintype.card A) :
    ∃ state : RelationPartialMatching.HoleState r,
      state.hole ≠ (state.move natural hnatural).hole ∧
        natural state.hole = natural (state.move natural hnatural).hole := by
  classical
  letI : Fintype (RelationPartialMatching.HoleState r) :=
    instFintypeRelationPartialMatchingHoleState r
  obtain ⟨initial⟩ := RelationPartialMatching.exists_holeState_of_card_lt
    r hcard
  obtain ⟨state, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (RelationPartialMatching.HoleState r))
    (fun s => (s.naturalSupport natural).card) ⟨initial, Finset.mem_univ _⟩
  refine ⟨state, state.hole_ne_move_hole natural hnatural, ?_⟩
  by_contra hne
  have hlt := state.card_naturalSupport_lt_move_of_ne
    natural hnatural hne
  have hle := hmax (state.move natural hnatural) (Finset.mem_univ _)
  omega


theorem RelationPartialMatching.HoleState.move_move_hole_eq_of_natural_eq
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (heq : natural state.hole =
      natural (state.move natural hnatural).hole) :
    ((state.move natural hnatural).move natural hnatural).hole =
      state.hole := by
  let moved := state.move natural hnatural
  apply moved.matching.injective_some
    (moved.matching_apply_move_hole natural hnatural)
  exact (state.move_matching_apply_hole natural hnatural).trans
    (congrArg some heq)


theorem RelationPartialMatching.HoleState.iterate_matching_apply_next_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) (n : Nat) :
    let move := RelationPartialMatching.HoleState.move natural hnatural
    (move^[n] state).matching.toFun (move^[n + 1] state).hole =
      some (natural (move^[n] state).hole) := by
  dsimp only
  let move := RelationPartialMatching.HoleState.move natural hnatural
  have hsucc : move^[n + 1] state = move (move^[n] state) := by
    rw [show n + 1 = Nat.succ n by omega]
    exact Function.iterate_succ_apply' move n state
  rw [hsucc]
  exact (move^[n] state).matching_apply_move_hole natural hnatural


theorem RelationPartialMatching.HoleState.iterate_succ_matching_apply_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) (n : Nat) :
    let move := RelationPartialMatching.HoleState.move natural hnatural
    (move^[n + 1] state).matching.toFun (move^[n] state).hole =
      some (natural (move^[n] state).hole) := by
  dsimp only
  let move := RelationPartialMatching.HoleState.move natural hnatural
  have hsucc : move^[n + 1] state = move (move^[n] state) := by
    rw [show n + 1 = Nat.succ n by omega]
    exact Function.iterate_succ_apply' move n state
  rw [hsucc]
  exact (move^[n] state).move_matching_apply_hole natural hnatural


theorem RelationPartialMatching.HoleState.iterate_matching_apply_eq_of_avoids
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (start stop : Nat) (hstartStop : start ≤ stop) (x : A)
    (havoids : ∀ n : Nat, start ≤ n -> n < stop ->
      x ≠ ((RelationPartialMatching.HoleState.move
          natural hnatural)^[n] state).hole ∧
        x ≠ ((RelationPartialMatching.HoleState.move
          natural hnatural)^[n + 1] state).hole) :
    ((RelationPartialMatching.HoleState.move
        natural hnatural)^[stop] state).matching.toFun x =
      ((RelationPartialMatching.HoleState.move
        natural hnatural)^[start] state).matching.toFun x := by
  let move := RelationPartialMatching.HoleState.move natural hnatural
  change (move^[stop] state).matching.toFun x =
    (move^[start] state).matching.toFun x
  induction stop, hstartStop using Nat.le_induction with
  | base => rfl
  | succ stop hstartLe hprevious =>
      have hstep : move^[stop + 1] state = move (move^[stop] state) := by
        rw [show stop + 1 = Nat.succ stop by omega]
        exact Function.iterate_succ_apply' move stop state
      have havoid := havoids stop hstartLe (by omega)
      have hxNext : x ≠ (move (move^[stop] state)).hole := by
        rw [← hstep]
        exact havoid.2
      calc
        (move^[stop + 1] state).matching.toFun x =
            (move^[stop] state).matching.toFun x := by
          rw [hstep]
          exact (move^[stop] state).move_matching_apply_of_ne
            natural hnatural x havoid.1 hxNext
        _ = (move^[start] state).matching.toFun x := by
          apply hprevious
          intro n hnStart hnStop
          exact havoids n hnStart (hnStop.trans_le (Nat.le_succ stop))


theorem RelationPartialMatching.HoleState.first_repeat_interior_matching
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((RelationPartialMatching.HoleState.move
          natural hnatural)^[start] state).hole =
        ((RelationPartialMatching.HoleState.move
          natural hnatural)^[stop] state).hole)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((RelationPartialMatching.HoleState.move
          natural hnatural)^[a] state).hole ≠
        ((RelationPartialMatching.HoleState.move
          natural hnatural)^[b] state).hole)
    (q : Nat) (hqStart : start < q) (hqStop : q < stop) :
    ((RelationPartialMatching.HoleState.move
        natural hnatural)^[stop] state).matching.toFun
          (((RelationPartialMatching.HoleState.move
            natural hnatural)^[q] state).hole) =
      some (natural
        (((RelationPartialMatching.HoleState.move
          natural hnatural)^[q] state).hole)) := by
  let move := RelationPartialMatching.HoleState.move natural hnatural
  change (move^[stop] state).matching.toFun (move^[q] state).hole =
    some (natural (move^[q] state).hole)
  have hassigned :=
    RelationPartialMatching.HoleState.iterate_succ_matching_apply_hole
      natural hnatural state q
  change (move^[q + 1] state).matching.toFun (move^[q] state).hole =
    some (natural (move^[q] state).hole) at hassigned
  have hretained :=
    RelationPartialMatching.HoleState.iterate_matching_apply_eq_of_avoids
      natural hnatural state (q + 1) stop (by omega)
        (move^[q] state).hole
  rw [hretained]
  · exact hassigned
  · intro n hnStart hnStop
    constructor
    · exact hdistinct q n (by omega) hnStop
    · by_cases hn : n + 1 < stop
      · exact hdistinct q (n + 1) (by omega) hn
      · have hnEq : n + 1 = stop := by omega
        rw [hnEq, ← hrepeat]
        exact (hdistinct start q hqStart hqStop).symm


theorem RelationPartialMatching.HoleState.first_repeat_interior_natural_ne
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((RelationPartialMatching.HoleState.move
          natural hnatural)^[start] state).hole =
        ((RelationPartialMatching.HoleState.move
          natural hnatural)^[stop] state).hole)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((RelationPartialMatching.HoleState.move
          natural hnatural)^[a] state).hole ≠
        ((RelationPartialMatching.HoleState.move
          natural hnatural)^[b] state).hole)
    (q u : Nat) (hqStart : start < q) (hqStop : q < stop)
    (huStart : start < u) (huStop : u < stop) (hqu : q ≠ u) :
    natural (((RelationPartialMatching.HoleState.move
        natural hnatural)^[q] state).hole) ≠
      natural (((RelationPartialMatching.HoleState.move
        natural hnatural)^[u] state).hole) := by
  let move := RelationPartialMatching.HoleState.move natural hnatural
  change natural (move^[q] state).hole ≠ natural (move^[u] state).hole
  intro hnaturalEq
  have hqMatch :=
    RelationPartialMatching.HoleState.first_repeat_interior_matching
      natural hnatural state start stop hstartStop hrepeat hdistinct
        q hqStart hqStop
  have huMatch :=
    RelationPartialMatching.HoleState.first_repeat_interior_matching
      natural hnatural state start stop hstartStop hrepeat hdistinct
        u huStart huStop
  have hholes : (move^[q] state).hole = (move^[u] state).hole :=
    (move^[stop] state).matching.injective_some hqMatch
      (huMatch.trans (congrArg some hnaturalEq.symm))
  rcases lt_or_gt_of_ne hqu with hqu' | huq'
  · exact (hdistinct q u hqu' huStop) hholes
  · exact (hdistinct u q huq' hqStop) hholes.symm


theorem RelationPartialMatching.HoleState.exists_minimal_hole_repeat
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    let move := RelationPartialMatching.HoleState.move natural hnatural
    ∃ start stop : Nat, start < stop ∧ stop ≤ Fintype.card A ∧
      (move^[start] state).hole = (move^[stop] state).hole ∧
      ∀ a b : Nat, a < b -> b < stop ->
        (move^[a] state).hole ≠ (move^[b] state).hole := by
  classical
  dsimp only
  let move := RelationPartialMatching.HoleState.move natural hnatural
  let exposed : Fin (Fintype.card A + 1) -> A := fun n =>
    (move^[n.1] state).hole
  have hnotinj : ¬Function.Injective exposed := by
    intro hinj
    have hcard := Fintype.card_le_of_injective exposed hinj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨u, v, heq, huv⟩ := Function.not_injective_iff.mp hnotinj
  obtain ⟨i0, j0, hij0, heq0, hj0Bound⟩ :
      ∃ i0 j0 : Nat, i0 < j0 ∧
        (move^[i0] state).hole = (move^[j0] state).hole ∧
        j0 ≤ Fintype.card A := by
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · exact ⟨u.1, v.1, huv', heq, Nat.le_of_lt_succ v.2⟩
    · exact ⟨v.1, u.1, hvu', heq.symm, Nat.le_of_lt_succ u.2⟩
  let P := fun n : Nat => ∃ i < n,
    (move^[i] state).hole = (move^[n] state).hole
  have hP : ∃ n, P n := ⟨j0, i0, hij0, heq0⟩
  let stop := Nat.find hP
  obtain ⟨start, hstartStop, hrepeat⟩ := Nat.find_spec hP
  have hstopBound : stop ≤ Fintype.card A := by
    exact (Nat.find_min' hP ⟨i0, hij0, heq0⟩).trans hj0Bound
  refine ⟨start, stop, hstartStop, hstopBound, hrepeat, ?_⟩
  intro a b hab hbStop habHole
  have hPb : P b := ⟨a, hab, habHole⟩
  have hstopLe := Nat.find_min' hP hPb
  exact (Nat.not_le_of_lt hbStop) hstopLe


theorem card_subtype_le_of_tag_preserving_fiberwise_discrepancy
    {A S : Type*} [Fintype A] (P Q : A -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (sourceTag : {a : A // P a ∧ ¬ Q a} -> S)
    (targetTag : {a : A // ¬ P a ∧ Q a} -> S)
    (f : {a : A // P a ∧ ¬ Q a} -> {a : A // ¬ P a ∧ Q a})
    (htag : ∀ x, targetTag (f x) = sourceTag x)
    (hfiber : ∀ s, Function.Injective fun
      x : {x : {a : A // P a ∧ ¬ Q a} // sourceTag x = s} => f x.1) :
    Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} := by
  exact card_subtype_le_of_discrepancyEmbedding P Q
    (embeddingOf_tag_preserving_fiberwise sourceTag targetTag f htag hfiber)


end StatMech.FrontierA
