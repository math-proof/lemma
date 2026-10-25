/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part4
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

theorem FiniteRelationMinimalTightProblem.tokenCarrier_card_lt_stateCarrier
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    Fintype.card problem.TokenCarrier <
      Fintype.card problem.StateCarrier := by
  have htight := problem.deficiency_one
  simpa only [FiniteRelationMinimalTightProblem.TokenCarrier,
    FiniteRelationMinimalTightProblem.StateCarrier, Fintype.card_coe] using
      (show (finiteBipartiteRelationNeighborhood
        problem.incident problem.carrier).card < problem.carrier.card by
        omega)


theorem FiniteRelationMinimalTightProblem.exists_holeState
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    Nonempty (StatMech.FrontierA.RelationPartialMatching.HoleState
      problem.restrictedIncident) :=
  StatMech.FrontierA.RelationPartialMatching.exists_holeState_of_card_lt
    problem.restrictedIncident problem.tokenCarrier_card_lt_stateCarrier


theorem FiniteRelationMinimalTightProblem.strongInductionWithHoleState
    (motive : FiniteRelationMinimalTightProblem.{u, v} -> Prop)
    (step : ∀ problem,
      Nonempty (StatMech.FrontierA.RelationPartialMatching.HoleState
        problem.restrictedIncident) ->
      (∀ smaller, smaller.rank < problem.rank -> motive smaller) ->
        motive problem)
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    motive problem := by
  apply problem.strongInduction motive
  intro current ih
  exact step current current.exists_holeState ih


theorem exists_external_incident_of_tight_properHall
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) [DecidableRel related]
    (htight : Fintype.card B + 1 = Fintype.card A)
    (hproper : ∀ smaller : Finset A, smaller ⊂ Finset.univ ->
      smaller.card ≤
        (Finset.univ.filter fun token =>
          ∃ source ∈ smaller, related source token).card)
    (size : Nat) (hsize : 0 < size)
    (states : Fin size ↪ A) (tokens : Fin size ↪ B) :
    ∃ i : Fin size, ∃ source : A,
      (∀ q, source ≠ states q) ∧ related source (tokens i) := by
  classical
  let stateBlock : Finset A := Finset.univ.map states
  let tokenBlock : Finset B := Finset.univ.map tokens
  let remaining : Finset A := Finset.univ \ stateBlock
  by_contra hno
  have havoid : ∀ source ∈ remaining, ∀ token ∈ tokenBlock,
      ¬ related source token := by
    intro source hsource token htoken hrelated
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp htoken
    apply hno
    refine ⟨i, source, ?_, hrelated⟩
    intro q hsourceEq
    exact (Finset.mem_sdiff.mp hsource).2
      (Finset.mem_map.mpr
        ⟨q, Finset.mem_univ q, hsourceEq.symm⟩)
  let first : Fin size := ⟨0, hsize⟩
  have hremainingProper : remaining ⊂ (Finset.univ : Finset A) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hfirstRemaining : states first ∈ remaining := by
      rw [heq]
      exact Finset.mem_univ _
    exact (Finset.mem_sdiff.mp hfirstRemaining).2
      (Finset.mem_map.mpr ⟨first, Finset.mem_univ first, rfl⟩)
  let neighborhood : Finset A -> Finset B := fun family =>
    Finset.univ.filter fun token =>
      ∃ source ∈ family, related source token
  have hneighborhoodSubset : neighborhood remaining ⊆
      Finset.univ \ tokenBlock := by
    intro token htoken
    obtain ⟨_huniv, source, hsource, hrelated⟩ :=
      Finset.mem_filter.mp htoken
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ token, fun htokenBlock =>
      havoid source hsource token htokenBlock hrelated⟩
  have hhall : remaining.card ≤ (neighborhood remaining).card := by
    exact hproper remaining hremainingProper
  have hneighborhoodCard : (neighborhood remaining).card ≤
      (Finset.univ \ tokenBlock).card :=
    Finset.card_le_card hneighborhoodSubset
  have hstateBlockCard : stateBlock.card = size := by
    simpa only [stateBlock, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have htokenBlockCard : tokenBlock.card = size := by
    simpa only [tokenBlock, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have hremainingCard : remaining.card = Fintype.card A - size := by
    change (Finset.univ \ stateBlock).card = Fintype.card A - size
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ stateBlock),
      Finset.card_univ, hstateBlockCard]
  have htokenRemainingCard : (Finset.univ \ tokenBlock).card =
      Fintype.card B - size := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ tokenBlock),
      Finset.card_univ, htokenBlockCard]
  have hsizeB : size ≤ Fintype.card B := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective tokens tokens.injective
  rw [hremainingCard] at hhall
  rw [htokenRemainingCard] at hneighborhoodCard
  omega


theorem finiteEmbedding_add_fresh
    {A : Type*} (size : Nat) (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) :
    Nonempty (Fin (size + 1) ↪ A) := by
  let f : Fin size ⊕ Fin 1 → A
    | Sum.inl i => block i
    | Sum.inr _ => extra
  have hinjective : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (block.injective hxy)
        | inr y => exact False.elim (hfresh x hxy.symm)
    | inr x =>
        cases y with
        | inl y => exact False.elim (hfresh y hxy)
        | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)
  let extended : Fin size ⊕ Fin 1 ↪ A := ⟨f, hinjective⟩
  exact ⟨(finSumFinEquiv (m := size) (n := 1)).symm.toEmbedding.trans extended⟩


theorem finiteEmbedding_snoc
    {A : Type*} (size : Nat) (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) :
    ∃ extended : Fin (size + 1) ↪ A,
      (∀ i, extended i.castSucc = block i) ∧
      extended (Fin.last size) = extra := by
  let f : Fin (size + 1) -> A :=
    Fin.lastCases extra (fun i => block i)
  have hinjective : Function.Injective f := by
    intro x
    refine Fin.lastCases ?_ (fun i => ?_) x
    · intro y
      refine Fin.lastCases ?_ (fun q h => ?_) y
      · intro _
        rfl
      · exact False.elim (hfresh q (by simpa only [f,
          Fin.lastCases_last, Fin.lastCases_castSucc] using h))
    · intro y
      refine Fin.lastCases ?_ (fun q h => ?_) y
      · intro h
        exact False.elim (hfresh i (by simpa only [f,
          Fin.lastCases_last, Fin.lastCases_castSucc] using h.symm))
      · exact congrArg Fin.castSucc (block.injective (by simpa only [f,
          Fin.lastCases_castSucc] using h))
  let extended : Fin (size + 1) ↪ A := ⟨f, hinjective⟩
  refine ⟨extended, ?_, ?_⟩
  · intro i
    change f i.castSucc = block i
    exact Fin.lastCases_castSucc i
  · change f (Fin.last size) = extra
    exact Fin.lastCases_last


end StatMech.GrahamGHS.FourColor
