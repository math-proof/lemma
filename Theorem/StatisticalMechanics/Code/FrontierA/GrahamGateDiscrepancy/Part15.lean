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
import Def.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part13


namespace StatMech.FrontierA

theorem finiteCommonClosureIter_subset_succ
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (n : Nat) :
    finiteCommonClosureIter P Q R S n ⊆
      finiteCommonClosureIter P Q R S (n + 1) := by
  rw [finiteCommonClosureIter]
  exact subset_finiteCommonClosureStep P Q R _

theorem finiteCommonClosureIter_zero_subset
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (n : Nat) :
    S ⊆ finiteCommonClosureIter P Q R S n := by
  induction n with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
      exact ih.trans (finiteCommonClosureIter_subset_succ P Q R S n)

theorem finiteCommonClosureIter_preserves_left
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (hS : ∀ x ∈ S, P x) :
    ∀ n x, x ∈ finiteCommonClosureIter P Q R S n -> P x := by
  intro n
  induction n with
  | zero => exact fun x hx => hS x hx
  | succ n ih =>
      intro x hx
      rw [finiteCommonClosureIter] at hx
      rcases (mem_finiteCommonClosureStep P Q R _ x).mp hx with hx | hx
      · exact ih x hx
      · exact hx.2.1


theorem finiteCommonClosureIter_common_mem_neighborhood
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (hS : ∀ x ∈ S, ¬ Q x) :
    ∀ n x, x ∈ finiteCommonClosureIter P Q R S n -> Q x ->
      x ∈ finiteRelationNeighborhood R
        (finiteCommonClosureIter P Q R S n) := by
  classical
  intro n
  induction n with
  | zero =>
      intro x hx hxQ
      exact False.elim (hS x hx hxQ)
  | succ n ih =>
      intro x hx hxQ
      rw [finiteCommonClosureIter] at hx ⊢
      rcases (mem_finiteCommonClosureStep P Q R _ x).mp hx with
        hxOld | hxNew
      · exact finiteRelationNeighborhood_mono R
          (finiteCommonClosureIter_subset_succ P Q R S n)
          (ih x hxOld hxQ)
      · exact finiteRelationNeighborhood_mono R
          (finiteCommonClosureIter_subset_succ P Q R S n) hxNew.1

theorem finiteCommonClosureIter_succ_start
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (n : Nat) :
    finiteCommonClosureIter P Q R S (n + 1) =
      finiteCommonClosureIter P Q R
        (finiteCommonClosureStep P Q R S) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change finiteCommonClosureStep P Q R
          (finiteCommonClosureIter P Q R S (n + 1)) =
        finiteCommonClosureStep P Q R
          (finiteCommonClosureIter P Q R
            (finiteCommonClosureStep P Q R S) n)
      rw [ih]


theorem exists_finiteCommonClosureIter_fixed
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) :
    ∃ n ≤ Fintype.card A - S.card,
      finiteCommonClosureIter P Q R S (n + 1) =
        finiteCommonClosureIter P Q R S n := by
  classical
  by_cases hfixed : finiteCommonClosureStep P Q R S = S
  · exact ⟨0, Nat.zero_le _, hfixed⟩
  · let S' := finiteCommonClosureStep P Q R S
    have hsubset : S ⊂ S' :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨subset_finiteCommonClosureStep P Q R S,
          fun h => hfixed h.symm⟩
    have hcard : S.card < S'.card := Finset.card_lt_card hsubset
    have hS'le : S'.card ≤ Fintype.card A := by
      simpa only [Finset.card_univ] using Finset.card_le_univ S'
    have hremaining : Fintype.card A - S'.card <
        Fintype.card A - S.card := by
      omega
    obtain ⟨n, hn, hstep⟩ :=
      exists_finiteCommonClosureIter_fixed P Q R S'
    refine ⟨n + 1, ?_, ?_⟩
    · omega
    · calc
        finiteCommonClosureIter P Q R S (n + 1 + 1) =
            finiteCommonClosureIter P Q R S' (n + 1) := by
          simpa only [S'] using
            finiteCommonClosureIter_succ_start P Q R S (n + 1)
        _ = finiteCommonClosureIter P Q R S' n := hstep
        _ = finiteCommonClosureIter P Q R S (n + 1) := by
          simpa only [S'] using
            (finiteCommonClosureIter_succ_start P Q R S n).symm
termination_by Fintype.card A - S.card
decreasing_by exact hremaining


theorem card_leftOnly_le_rightOnly_of_commonClosed_expansion
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (T : Finset A)
    (hrel : ∀ {x y}, R x y -> P x ∧ Q y)
    (hnegative : Finset.univ.filter (fun x => P x ∧ ¬ Q x) ⊆ T)
    (hleft : ∀ x ∈ T, P x)
    (hclosed : finiteCommonClosureStep P Q R T = T)
    (hexpand : T.card ≤ (finiteRelationNeighborhood R T).card) :
    (Finset.univ.filter fun x => P x ∧ ¬ Q x).card ≤
      (Finset.univ.filter fun x => ¬ P x ∧ Q x).card := by
  classical
  let N := Finset.univ.filter fun x => P x ∧ ¬ Q x
  let Pos := Finset.univ.filter fun x => ¬ P x ∧ Q x
  let TC := T.filter Q
  let U := finiteRelationNeighborhood R T
  let UC := U.filter P
  let UP := U.filter fun x => ¬ P x
  have hTdecomp : T = N ∪ TC := by
    ext x
    constructor
    · intro hx
      by_cases hxQ : Q x
      · exact Finset.mem_union_right N (Finset.mem_filter.mpr ⟨hx, hxQ⟩)
      · exact Finset.mem_union_left TC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hleft x hx, hxQ⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxN | hxTC
      · exact hnegative hxN
      · exact (Finset.mem_filter.mp hxTC).1
  have hN_TC : Disjoint N TC := by
    rw [Finset.disjoint_left]
    intro x hxN hxTC
    exact (Finset.mem_filter.mp hxN).2.2 (Finset.mem_filter.mp hxTC).2
  have hTcard : T.card = N.card + TC.card := by
    rw [hTdecomp, Finset.card_union_of_disjoint hN_TC]
  have hUQ : ∀ x ∈ U, Q x := by
    intro y hy
    obtain ⟨x, -, hxy⟩ := Finset.mem_filter.mp hy |>.2
    exact (hrel hxy).2
  have hUdecomp : U = UP ∪ UC := by
    ext x
    constructor
    · intro hx
      by_cases hxP : P x
      · exact Finset.mem_union_right UP (Finset.mem_filter.mpr ⟨hx, hxP⟩)
      · exact Finset.mem_union_left UC (Finset.mem_filter.mpr ⟨hx, hxP⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxUP | hxUC
      · exact (Finset.mem_filter.mp hxUP).1
      · exact (Finset.mem_filter.mp hxUC).1
  have hUP_UC : Disjoint UP UC := by
    rw [Finset.disjoint_left]
    intro x hxUP hxUC
    exact (Finset.mem_filter.mp hxUP).2 (Finset.mem_filter.mp hxUC).2
  have hUcard : U.card = UP.card + UC.card := by
    rw [hUdecomp, Finset.card_union_of_disjoint hUP_UC]
  have hUC_TC : UC ⊆ TC := by
    intro x hx
    have hxU := (Finset.mem_filter.mp hx).1
    have hxP := (Finset.mem_filter.mp hx).2
    have hxQ := hUQ x hxU
    have hxStep : x ∈ finiteCommonClosureStep P Q R T := by
      exact (mem_finiteCommonClosureStep P Q R T x).mpr
        (Or.inr ⟨hxU, hxP, hxQ⟩)
    exact Finset.mem_filter.mpr ⟨hclosed ▸ hxStep, hxQ⟩
  have hUP_Pos : UP ⊆ Pos := by
    intro x hx
    have hxU := (Finset.mem_filter.mp hx).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      (Finset.mem_filter.mp hx).2, hUQ x hxU⟩
  have hUCcard := Finset.card_le_card hUC_TC
  have hUPcard := Finset.card_le_card hUP_Pos
  rw [hTcard, hUcard] at hexpand
  change N.card ≤ Pos.card
  omega

end StatMech.FrontierA
