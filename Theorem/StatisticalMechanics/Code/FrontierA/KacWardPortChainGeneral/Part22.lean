/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part22
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwOrderedDecreasingInternalDartFrom_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G) (h : 0 < kwOrderedPortRank order p) :
    (kwOrderedDecreasingInternalDartFrom G order p h).1.fst = p := by
  change ((kwOrderedInternalSplitDartEquiv G order).symm
    ⟨(p, kwOrderedPortAtRank order p.1
      ⟨kwOrderedPortRank order p - 1, _⟩), _⟩).1.fst = p
  rfl

@[simp] theorem kwOrderedDecreasingInternalDartFrom_rank_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G) (h : 0 < kwOrderedPortRank order p) :
    kwOrderedPortRank order
        (kwOrderedDecreasingInternalDartFrom G order p h).1.snd + 1 =
      kwOrderedPortRank order p := by
  change kwOrderedPortRank order (kwOrderedPortAtRank order p.1
    ⟨kwOrderedPortRank order p - 1, _⟩) + 1 = _
  simp
  omega

theorem kwOrderedIncreasingInternalDartFrom_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p q : KWDartPort G) (hpq : p.1 = q.1)
    (hlt : kwOrderedPortRank order p < kwOrderedPortRank order q)
    (hbound : kwOrderedPortRank order p + 1 <
      Fintype.card (KWOutgoingDart (G := G) p.1)) :
    KWOrderedInternalDartFacesPort order
      (kwOrderedIncreasingInternalDartFrom G order p hbound) q := by
  unfold KWOrderedInternalDartFacesPort
  constructor
  · change p.1 = q.1
    exact hpq
  · left
    constructor
    · rw [kwOrderedIncreasingInternalDartFrom_fst,
        kwOrderedIncreasingInternalDartFrom_rank_snd]
      omega
    · rw [kwOrderedIncreasingInternalDartFrom_rank_snd]
      omega

theorem kwOrderedDecreasingInternalDartFrom_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p q : KWDartPort G) (hpq : p.1 = q.1)
    (hlt : kwOrderedPortRank order q < kwOrderedPortRank order p)
    (hbound : 0 < kwOrderedPortRank order p) :
    KWOrderedInternalDartFacesPort order
      (kwOrderedDecreasingInternalDartFrom G order p hbound) q := by
  unfold KWOrderedInternalDartFacesPort
  constructor
  · change p.1 = q.1
    exact hpq
  · right
    constructor
    · rw [kwOrderedDecreasingInternalDartFrom_fst]
      have hs := kwOrderedDecreasingInternalDartFrom_rank_snd
        G order p hbound
      omega
    · have hs := kwOrderedDecreasingInternalDartFrom_rank_snd
        G order p hbound
      omega

theorem kwOrderedInternalDartStep_increasingFrom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order)
    (hd : kwOrderedPortRank order d.1.fst <
      kwOrderedPortRank order d.1.snd)
    (hbound : kwOrderedPortRank order d.1.snd + 1 <
      Fintype.card (KWOutgoingDart (G := G) d.1.snd.1)) :
    KWOrderedInternalDartStep G order d
      (kwOrderedIncreasingInternalDartFrom G order d.1.snd hbound) := by
  constructor
  · simp
  · intro hedge
    rw [SimpleGraph.dart_edge_eq_iff] at hedge
    have hddata := kwOrderedInternalSplitDart_adj_data G order d
    rcases hedge with hedge | hedge
    · have h := congrArg (fun delta :
          (kwOrderedDartPortSplitGraph G order).Dart ↦
          kwOrderedPortRank order delta.snd) hedge
      simp only [kwOrderedIncreasingInternalDartFrom_rank_snd] at h
      omega
    · have h := congrArg (fun delta :
          (kwOrderedDartPortSplitGraph G order).Dart ↦
          kwOrderedPortRank order delta.fst) hedge
      change kwOrderedPortRank order d.1.fst =
        kwOrderedPortRank order
          (kwOrderedIncreasingInternalDartFrom G order
            d.1.snd hbound).1.snd at h
      rw [kwOrderedIncreasingInternalDartFrom_rank_snd] at h
      rcases hddata.2 with hinc | hdec <;> omega

theorem kwOrderedInternalDartStep_decreasingFrom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order)
    (hd : kwOrderedPortRank order d.1.snd <
      kwOrderedPortRank order d.1.fst)
    (hbound : 0 < kwOrderedPortRank order d.1.snd) :
    KWOrderedInternalDartStep G order d
      (kwOrderedDecreasingInternalDartFrom G order d.1.snd hbound) := by
  constructor
  · simp
  · intro hedge
    rw [SimpleGraph.dart_edge_eq_iff] at hedge
    have hddata := kwOrderedInternalSplitDart_adj_data G order d
    rcases hedge with hedge | hedge
    · have h := congrArg (fun delta :
          (kwOrderedDartPortSplitGraph G order).Dart ↦
          kwOrderedPortRank order delta.snd) hedge
      have hs := kwOrderedDecreasingInternalDartFrom_rank_snd
        G order d.1.snd hbound
      simp only at h
      change kwOrderedPortRank order d.1.snd =
        kwOrderedPortRank order
          (kwOrderedDecreasingInternalDartFrom G order
            d.1.snd hbound).1.snd at h
      omega
    · have h := congrArg (fun delta :
          (kwOrderedDartPortSplitGraph G order).Dart ↦
          kwOrderedPortRank order delta.fst) hedge
      change kwOrderedPortRank order d.1.fst =
        kwOrderedPortRank order
          (kwOrderedDecreasingInternalDartFrom G order
            d.1.snd hbound).1.snd at h
      have hs := kwOrderedDecreasingInternalDartFrom_rank_snd
        G order d.1.snd hbound
      rcases hddata.2 with hinc | hdec <;> omega


theorem kwAngularSplit_internalBlock_apply_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G
      (kwAngularPortOrder embedding))
    (hstep : KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d e) :
    kwOrderedSplitInternalBlock G (kwAngularPortOrder embedding)
        (kwGraphTransition
          (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
          (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)) d e =
      1 := by
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inr]
  change d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge at hstep
  rw [if_pos hstep,
    kwOrderedSplitWeight_internal G weight
      (kwAngularPortOrder embedding) d,
    kwAngularSplitPhase_internal_internal]
  exact one_mul 1


theorem kwAngularSplit_internalBlock_apply_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G
      (kwAngularPortOrder embedding))
    (hstep : ¬KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d e) :
    kwOrderedSplitInternalBlock G (kwAngularPortOrder embedding)
        (kwGraphTransition
          (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
          (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)) d e =
      0 := by
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inr]
  change ¬(d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge) at hstep
  rw [if_neg hstep]

theorem kwOrderedExternalSplitDart_edge_ne_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : G.Dart) (e : KWOrderedInternalSplitDart G order) :
    (kwOrderedExternalSplitDartOfDart G order d).1.edge ≠ e.1.edge := by
  intro hedge
  rw [SimpleGraph.dart_edge_eq_iff] at hedge
  rcases hedge with hedge | hedge
  · apply e.2
    rw [← hedge]
    exact (kwOrderedExternalSplitDartOfDart G order d).2
  · apply e.2
    have hmatch := (kwOrderedExternalSplitDartOfDart G order d).2
    rw [hedge] at hmatch
    have hs := congrArg SimpleGraph.Dart.symm hmatch
    simpa using hs.symm


theorem kwAngularSplit_enterBlock_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hconnect : kwPortOfDart G d.symm = e.1.fst) :
    (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding))).toBlocks₁₂ d e =
      weight d.edge * kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 e.1 := by
  unfold Matrix.toBlocks₁₂ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_pos ⟨by simpa using hconnect, by
      exact kwOrderedExternalSplitDart_edge_ne_internal G
        (kwAngularPortOrder embedding) d e⟩,
    kwOrderedSplitWeight_matching]

theorem kwAngularSplit_enterBlock_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
    (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding))).toBlocks₁₂ d e = 0 := by
  unfold Matrix.toBlocks₁₂ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_neg (by
    intro h
    apply hconnect
    simpa using h.1)]


theorem kwAngularSplit_exitBlock_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hconnect : d.1.snd = kwPortOfDart G e) :
    (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding))).toBlocks₂₁ d e =
      kwPortAngleRoot embedding (kwPortOfDart G e) := by
  unfold Matrix.toBlocks₂₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_pos ⟨by simpa using hconnect,
      (kwOrderedExternalSplitDart_edge_ne_internal G
        (kwAngularPortOrder embedding) e d).symm⟩,
    kwOrderedSplitWeight_internal, kwAngularSplitPhase_internal_external,
    one_mul]

theorem kwAngularSplit_exitBlock_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hconnect : d.1.snd ≠ kwPortOfDart G e) :
    (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding))).toBlocks₂₁ d e = 0 := by
  unfold Matrix.toBlocks₂₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_neg (by
    intro h
    apply hconnect
    simpa using h.1)]


end StatMech.FrontierA
