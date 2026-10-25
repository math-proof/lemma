/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part5
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

@[simp] theorem finiteEmbedding_replaceAt_same
    {A : Type*} {size : Nat} (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) (index : Fin size) :
    finiteEmbedding_replaceAt block extra hfresh index index = extra := by
  change (if index = index then extra else block index) = extra
  rw [if_pos rfl]

theorem finiteEmbedding_replaceAt_ne
    {A : Type*} {size : Nat} (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) (index other : Fin size)
    (hne : other ≠ index) :
    finiteEmbedding_replaceAt block extra hfresh index other = block other := by
  change (if other = index then extra else block other) = block other
  rw [if_neg hne]


theorem finiteEmbedding_replaceAt_displaced_fresh
    {A : Type*} {size : Nat} (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) (index : Fin size) :
    ∀ other, block index ≠ finiteEmbedding_replaceAt block extra hfresh index other := by
  intro other
  by_cases hother : other = index
  · subst other
    rw [finiteEmbedding_replaceAt_same]
    exact (hfresh index).symm
  · rw [finiteEmbedding_replaceAt_ne block extra hfresh index other hother]
    intro heq
    exact hother (block.injective heq.symm)


theorem exists_fin_castSucc_eq_of_ne_last
    {size : Nat} (q : Fin (size + 1)) (hq : q ≠ Fin.last size) :
    ∃ i : Fin size, i.castSucc = q := by
  have hlt : q < Fin.last size := Fin.lt_last_iff_ne_last.mpr hq
  let i : Fin size := ⟨q.1, hlt⟩
  exact ⟨i, Fin.ext (by rfl)⟩


theorem exists_fin_castSucc_eq_left_or_right_of_ne
    {size : Nat} (q r : Fin (size + 1)) (hqr : q ≠ r) :
    ∃ i : Fin size, i.castSucc = q ∨ i.castSucc = r := by
  by_cases hq : q = Fin.last size
  · have hr : r ≠ Fin.last size := by
      intro hr
      exact hqr (hq.trans hr.symm)
    obtain ⟨i, hi⟩ := exists_fin_castSucc_eq_of_ne_last r hr
    exact ⟨i, Or.inr hi⟩
  · obtain ⟨i, hi⟩ := exists_fin_castSucc_eq_of_ne_last q hq
    exact ⟨i, Or.inl hi⟩


theorem saturatedHoleState_sourceEmbedding_add_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (size : Nat) (tokens : Fin size ↪ B) :
    Nonempty (Fin (size + 1) ↪ A) := by
  classical
  let preimage : B ↪ A :=
    ⟨state.matching.targetPreimage hsaturated,
      state.matching.targetPreimage_injective hsaturated⟩
  let occupants : Fin size ↪ A := tokens.trans preimage
  have hfresh : ∀ i, state.hole ≠ occupants i := by
    intro i heq
    apply state.hole_unmatched
    apply (StatMech.FrontierA.RelationPartialMatching.mem_support_iff
      state.matching state.hole).2
    refine ⟨tokens i, ?_⟩
    rw [heq]
    exact state.matching.targetPreimage_spec hsaturated (tokens i)
  exact finiteEmbedding_add_fresh size occupants state.hole hfresh


theorem saturatedHoleState_targetPreimage_fresh_of_token_fresh
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (size : Nat) (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hmatched : ∀ i,
      state.matching.toFun (sources i) = some (tokens i))
    (fresh : B) (hfresh : ∀ i, fresh ≠ tokens i) :
    ∀ i, state.matching.targetPreimage hsaturated fresh ≠ sources i := by
  intro i heq
  apply hfresh i
  apply Option.some.inj
  exact (state.matching.targetPreimage_spec hsaturated fresh).symm.trans
    (heq ▸ hmatched i)


theorem saturatedHoleState_extendMatchedBlock
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (size : Nat) (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hmatched : ∀ i,
      state.matching.toFun (sources i) = some (tokens i))
    (fresh : B) (hfresh : ∀ i, fresh ≠ tokens i) :
    ∃ extendedSources : (Fin size ⊕ Fin 1) ↪ A,
      ∃ extendedTokens : (Fin size ⊕ Fin 1) ↪ B,
        (∀ q, state.matching.toFun (extendedSources q) =
          some (extendedTokens q)) ∧
        (∀ i, extendedSources (Sum.inl i) = sources i) ∧
        (∀ i, extendedTokens (Sum.inl i) = tokens i) ∧
        extendedTokens (Sum.inr 0) = fresh := by
  let newSource := state.matching.targetPreimage hsaturated fresh
  have hsourceFresh : ∀ i, newSource ≠ sources i :=
    saturatedHoleState_targetPreimage_fresh_of_token_fresh
      state hsaturated size sources tokens hmatched fresh hfresh
  let sourceMap : Fin size ⊕ Fin 1 -> A
    | Sum.inl i => sources i
    | Sum.inr _ => newSource
  have hsourceInjective : Function.Injective sourceMap := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (sources.injective hxy)
        | inr y => exact False.elim (hsourceFresh x hxy.symm)
    | inr x =>
        cases y with
        | inl y => exact False.elim (hsourceFresh y hxy)
        | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  let tokenMap : Fin size ⊕ Fin 1 -> B
    | Sum.inl i => tokens i
    | Sum.inr _ => fresh
  have htokenInjective : Function.Injective tokenMap := by
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
  let extendedSources : (Fin size ⊕ Fin 1) ↪ A :=
    ⟨sourceMap, hsourceInjective⟩
  let extendedTokens : (Fin size ⊕ Fin 1) ↪ B :=
    ⟨tokenMap, htokenInjective⟩
  refine ⟨extendedSources, extendedTokens, ?_, ?_, ?_, rfl⟩
  · intro q
    cases q with
    | inl i => exact hmatched i
    | inr i =>
        exact state.matching.targetPreimage_spec hsaturated fresh
  · intro i
    rfl
  · intro i
    rfl


theorem saturatedHoleState_alternatingPath_nextSource_fresh
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (size : Nat) (sources : Fin (size + 1) ↪ A)
    (tokens : Fin size ↪ B)
    (hhole : sources 0 = state.hole)
    (hmatched : ∀ i,
      state.matching.toFun (sources i.succ) = some (tokens i))
    (fresh : B) (hfresh : ∀ i, fresh ≠ tokens i) :
    ∀ q, state.matching.targetPreimage hsaturated fresh ≠ sources q := by
  intro q
  refine Fin.cases ?_ (fun i => ?_) q
  · intro heq
    apply state.hole_unmatched
    apply (StatMech.FrontierA.RelationPartialMatching.mem_support_iff
      state.matching state.hole).2
    refine ⟨fresh, ?_⟩
    rw [← hhole, ← heq]
    exact state.matching.targetPreimage_spec hsaturated fresh
  · intro heq
    apply hfresh i
    apply Option.some.inj
    exact (state.matching.targetPreimage_spec hsaturated fresh).symm.trans
      (heq ▸ hmatched i)


theorem saturatedHoleState_alternatingPath_close_or_extend
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState r)
    (hsaturated : ∀ token, ∃ source,
      state.matching.toFun source = some token)
    (successor : A -> B)
    (size : Nat) (sources : Fin (size + 1) ↪ A)
    (tokens : Fin size ↪ B)
    (hhole : sources 0 = state.hole)
    (htransition : ∀ i, tokens i = successor (sources i.castSucc))
    (hmatched : ∀ i,
      state.matching.toFun (sources i.succ) = some (tokens i)) :
    (∃ i, successor (sources (Fin.last size)) = tokens i ∧
      state.matching.targetPreimage hsaturated
          (successor (sources (Fin.last size))) = sources i.succ) ∨
      ∃ extendedSources : Fin (size + 2) ↪ A,
        ∃ extendedTokens : Fin (size + 1) ↪ B,
          extendedSources 0 = state.hole ∧
          (∀ i, extendedTokens i =
            successor (extendedSources i.castSucc)) ∧
          (∀ i, state.matching.toFun (extendedSources i.succ) =
            some (extendedTokens i)) ∧
          (∀ i, extendedSources i.castSucc = sources i) ∧
          (∀ i, extendedTokens i.castSucc = tokens i) := by
  let nextToken := successor (sources (Fin.last size))
  by_cases hrepeats : ∃ i, nextToken = tokens i
  · obtain ⟨i, hi⟩ := hrepeats
    left
    refine ⟨i, hi, ?_⟩
    apply state.matching.injective_some
    · exact state.matching.targetPreimage_spec hsaturated nextToken
    · exact (hmatched i).trans (congrArg some hi.symm)
  · have hfresh : ∀ i, nextToken ≠ tokens i := by
      intro i hi
      exact hrepeats ⟨i, hi⟩
    let nextSource := state.matching.targetPreimage hsaturated nextToken
    have hsourceFresh : ∀ q, nextSource ≠ sources q :=
      saturatedHoleState_alternatingPath_nextSource_fresh
        state hsaturated size sources tokens hhole hmatched nextToken hfresh
    obtain ⟨extendedSources, hsourcePrefix, hsourceLast⟩ :=
      finiteEmbedding_snoc (size + 1) sources nextSource hsourceFresh
    obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
      finiteEmbedding_snoc size tokens nextToken hfresh
    right
    refine ⟨extendedSources, extendedTokens, ?_, ?_, ?_,
      hsourcePrefix, htokenPrefix⟩
    · calc
        extendedSources 0 = sources 0 := hsourcePrefix 0
        _ = state.hole := hhole
    · intro i
      refine Fin.lastCases ?_ (fun q => ?_) i
      · calc
          extendedTokens (Fin.last size) = nextToken := htokenLast
          _ = successor (sources (Fin.last size)) := rfl
          _ = successor (extendedSources (Fin.last size).castSucc) :=
            congrArg successor (hsourcePrefix (Fin.last size)).symm
      · calc
          extendedTokens q.castSucc = tokens q := htokenPrefix q
          _ = successor (sources q.castSucc) := htransition q
          _ = successor (extendedSources q.castSucc.castSucc) :=
            congrArg successor (hsourcePrefix q.castSucc).symm
    · intro i
      refine Fin.lastCases ?_ (fun q => ?_) i
      · have hlastSucc : (Fin.last size).succ = Fin.last (size + 1) := by
          apply Fin.ext
          rfl
        rw [hlastSucc, hsourceLast, htokenLast]
        exact state.matching.targetPreimage_spec hsaturated nextToken
      · have hsuccCast : q.castSucc.succ = q.succ.castSucc := by
          apply Fin.ext
          rfl
        rw [hsuccCast, hsourcePrefix q.succ, htokenPrefix q]
        exact hmatched q


end StatMech.GrahamGHS.FourColor
