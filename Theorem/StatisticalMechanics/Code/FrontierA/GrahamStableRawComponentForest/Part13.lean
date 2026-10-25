/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part13
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

theorem finiteRelation_threeTwoOrbitCore_saturated_no_freshToken :
    let related : Fin 3 -> Fin 2 -> Prop := fun _ _ => True
    let family := FiniteRelationDeficiencyOneFamily.threeTwo
      (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (0 : Fin 2) 1 (by decide)
    family.IsSaturated related ∧
      related 0 0 ∧ related 1 0 ∧ related 0 1 ∧ related 2 1 ∧
      Nonempty (Fin 2 ↪ Fin 2) ∧ Nonempty (Fin 2 ↪ Fin 2) ∧
      ¬ ∃ token : Fin 2, token ∉ family.tokens := by
  dsimp [FiniteRelationDeficiencyOneFamily.threeTwo,
    FiniteRelationDeficiencyOneFamily.IsSaturated,
    FiniteRelationDeficiencyOneFamily.TokenSaturated,
    FiniteRelationDeficiencyOneFamily.SourceSaturated]
  constructor
  · constructor
    · intro source token _ _
      fin_cases source <;> simp
    · intro source token _ _
      fin_cases token <;> simp
  · refine ⟨by trivial, by trivial, by trivial, by trivial,
      ⟨Function.Embedding.refl _⟩, ⟨Function.Embedding.refl _⟩, ?_⟩
    simp


theorem finiteRelation_threeTwoOrbitCore_balancedBlock_not_tokenClosed :
    ∃ sources : Fin 1 ↪ Fin 3, ∃ tokens : Fin 1 ↪ Fin 2,
      ¬ FiniteRelationTokenClosed (fun _ _ => True) 1 sources tokens := by
  let sources : Fin 1 ↪ Fin 3 :=
    ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩
  let tokens : Fin 1 ↪ Fin 2 :=
    ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨sources, tokens, ?_⟩
  intro hclosed
  obtain ⟨i, hi⟩ := hclosed 1 0 trivial ⟨0, rfl⟩
  simp [sources] at hi


theorem finiteEmbeddingComplement_strictDeficit
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (size : Nat) (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hdeficit : Fintype.card B < Fintype.card A) :
    Fintype.card (FiniteEmbeddingComplement size tokens) <
      Fintype.card (FiniteEmbeddingComplement size sources) := by
  rw [finiteEmbeddingComplement_card, finiteEmbeddingComplement_card]
  have hsourceSize : size ≤ Fintype.card A := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective sources sources.injective
  have htokenSize : size ≤ Fintype.card B := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective tokens tokens.injective
  omega


theorem finiteEmbedding_strictBlock_prefix
    {B : Type*} [Fintype B] [DecidableEq B]
    (size : Nat) (tokens : Fin (size + 1) ↪ B) :
    ∃ initial : Fin size ↪ B,
      ∃ extra : FiniteEmbeddingComplement size initial,
        extra.1 = tokens (Fin.last size) := by
  let initial : Fin size ↪ B := Fin.castSuccEmb.trans tokens
  let extra : FiniteEmbeddingComplement size initial :=
    ⟨tokens (Fin.last size), by
      intro hmem
      obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
      exact Fin.castSucc_ne_last i (tokens.injective heq)⟩
  exact ⟨initial, extra, rfl⟩


theorem exists_closedBlock_of_strictExtension
    {Block : Type*} (capacity : Nat)
    (blockSize : Block -> Nat) (closed : Block -> Prop)
    (hbound : ∀ block, blockSize block ≤ capacity)
    (hextend : ∀ block, ¬ closed block ->
      ∃ extended, blockSize extended = blockSize block + 1)
    (start : Block) : ∃ block, closed block := by
  have aux : ∀ measure, ∀ current : Block,
      capacity - blockSize current = measure -> ∃ block, closed block := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
      intro current hmeasure
      by_cases hclosed : closed current
      · exact ⟨current, hclosed⟩
      · obtain ⟨extended, hextended⟩ := hextend current hclosed
        have hstrict : capacity - blockSize extended < measure := by
          have hextendedBound := hbound extended
          rw [← hmeasure]
          omega
        exact ih (capacity - blockSize extended) hstrict extended rfl
  exact aux (capacity - blockSize start) start rfl


theorem exists_sizeMaximalBlock
    {Block : Type*} (capacity : Nat) (blockSize : Block -> Nat)
    (hbound : ∀ block, blockSize block ≤ capacity) (start : Block) :
    ∃ block, ∀ other, blockSize other ≤ blockSize block := by
  classical
  have aux : ∀ measure, ∀ current : Block,
      capacity - blockSize current = measure ->
        ∃ block, ∀ other, blockSize other ≤ blockSize block := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
      intro current hmeasure
      by_cases hmax : ∀ other, blockSize other ≤ blockSize current
      · exact ⟨current, hmax⟩
      · push Not at hmax
        obtain ⟨larger, hlarger⟩ := hmax
        have hstrict : capacity - blockSize larger < measure := by
          have hlargerBound := hbound larger
          rw [← hmeasure]
          omega
        exact ih (capacity - blockSize larger) hstrict larger rfl
  exact aux (capacity - blockSize start) start rfl


theorem exists_fintype_score_maximal
    {A : Type*} [Fintype A] [Nonempty A] (score : A -> Nat) :
    ∃ best, ∀ other, score other ≤ score best := by
  classical
  let scores := Finset.univ.image score
  have hscores : scores.Nonempty := by
    let sample : A := Classical.choice inferInstance
    exact ⟨score sample, Finset.mem_image.mpr
      ⟨sample, Finset.mem_univ sample, rfl⟩⟩
  let maximum := scores.max' hscores
  have hmaximum : maximum ∈ scores := Finset.max'_mem scores hscores
  obtain ⟨best, _hbest, hscore⟩ := Finset.mem_image.mp hmaximum
  refine ⟨best, ?_⟩
  intro other
  rw [hscore]
  exact Finset.le_max' scores (score other)
    (Finset.mem_image.mpr ⟨other, Finset.mem_univ other, rfl⟩)


theorem finiteEmbedding_three_of_pairwise_ne
    {A : Type*} (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Nonempty (Fin 3 ↪ A) := by
  let f : Fin 3 -> A := fun i =>
    Fin.cases a (fun q => Fin.cases b (fun _ => c) q) i
  have hinjective : Function.Injective f := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hab hxy)
    · exact False.elim (hac hxy)
    · exact False.elim (hab hxy.symm)
    · rfl
    · exact False.elim (hbc hxy)
    · exact False.elim (hac hxy.symm)
    · exact False.elim (hbc hxy.symm)
    · rfl
  exact ⟨⟨f, hinjective⟩⟩


theorem finiteEmbedding_two_of_ne
    {A : Type*} (a b : A) (hab : a ≠ b) : Nonempty (Fin 2 ↪ A) := by
  let f : Fin 2 -> A := fun i => Fin.cases a (fun _ => b) i
  have hinjective : Function.Injective f := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hab hxy)
    · exact False.elim (hab hxy.symm)
    · rfl
  exact ⟨⟨f, hinjective⟩⟩


theorem tightProperHall_externalSource_freshToken_or_exhausts
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) [DecidableRel related]
    (hproper : ∀ smaller : Finset A, smaller ⊂ Finset.univ ->
      smaller.card ≤
        (Finset.univ.filter fun token =>
          ∃ source ∈ smaller, related source token).card)
    (size : Nat) (states : Fin size ↪ A)
    (external : A) (hexternal : ∀ i, external ≠ states i) :
    Nonempty (Fin (size + 1) ↪ B) ∨
      ∀ source : A, source = external ∨ ∃ i, source = states i := by
  classical
  let stateBlock : Finset A := Finset.univ.map states
  let extended := insert external stateBlock
  have hexternalNotMem : external ∉ stateBlock := by
    intro hmem
    obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
    exact hexternal i heq.symm
  have hextendedCard : extended.card = size + 1 := by
    rw [Finset.card_insert_of_notMem hexternalNotMem]
    simp only [stateBlock, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  by_cases hproperBlock : extended ⊂ (Finset.univ : Finset A)
  · left
    have hhall := hproper extended hproperBlock
    have hneighborhoodCard :
        (Finset.univ.filter fun token =>
          ∃ source ∈ extended, related source token).card ≤ Fintype.card B := by
      simpa only [Finset.card_univ] using Finset.card_le_univ
        (Finset.univ.filter fun token =>
          ∃ source ∈ extended, related source token)
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_fin, hextendedCard] using hhall.trans hneighborhoodCard
  · right
    have hextended : extended = (Finset.univ : Finset A) := by
      by_contra hne
      exact hproperBlock (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, hne⟩)
    intro source
    have hmem : source ∈ extended := by rw [hextended]; exact Finset.mem_univ _
    rcases Finset.mem_insert.mp hmem with heq | hstate
    · exact Or.inl heq
    · obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hstate
      exact Or.inr ⟨i, heq.symm⟩


theorem strictDeficit_sub_balancedBlock
    (self direct token block : Nat)
    (hblockDirect : block ≤ direct) (hblockToken : block ≤ token)
    (hdeficit : token < self + direct) :
    token - block < self + (direct - block) := by
  omega


theorem strictDeficit_sub_balancedEmbeddings
    {Self Direct Token : Type*} [Finite Self] [Finite Direct] [Finite Token]
    (block : Nat)
    (hdeficit : Nat.card Token < Nat.card Self + Nat.card Direct)
    (directBlock : Nonempty (Fin block ↪ Direct))
    (tokenBlock : Nonempty (Fin block ↪ Token)) :
    Nat.card Token - block < Nat.card Self + (Nat.card Direct - block) := by
  obtain ⟨directEmbedding⟩ := directBlock
  obtain ⟨tokenEmbedding⟩ := tokenBlock
  have hblockDirect : block ≤ Nat.card Direct := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      directEmbedding directEmbedding.injective
  have hblockToken : block ≤ Nat.card Token := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      tokenEmbedding tokenEmbedding.injective
  exact strictDeficit_sub_balancedBlock
    (Nat.card Self) (Nat.card Direct) (Nat.card Token) block
      hblockDirect hblockToken hdeficit


end StatMech.GrahamGHS.FourColor
