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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part15
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedSplitInternalBlock_reindex_eq_transition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    Matrix.reindex (kwOrderedInternalSplitDartEquiv G order)
        (kwOrderedInternalSplitDartEquiv G order)
        (kwOrderedSplitInternalBlock G order
          (kwGraphTransition (kwOrderedDartPortSplitGraph G order)
            weight phase)) =
      kwGraphTransition (kwOrderedPortInternalGraph G order) weight
        (kwOrderedInternalPhase G order phase) := by
  ext d e
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition kwOrderedInternalPhase
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl


theorem kwOrderedSplitInternalBlock_isNilpotent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    IsNilpotent (kwOrderedSplitInternalBlock G order
      (kwGraphTransition (kwOrderedDartPortSplitGraph G order)
        weight phase)) := by
  let B := kwOrderedSplitInternalBlock G order
    (kwGraphTransition (kwOrderedDartPortSplitGraph G order) weight phase)
  let e := kwOrderedInternalSplitDartEquiv G order
  let A := Matrix.reindexAlgEquiv ℂ ℂ e
  let T := kwGraphTransition (kwOrderedPortInternalGraph G order) weight
    (kwOrderedInternalPhase G order phase)
  have hAB : A B = T := by
    simpa only [A, B, T, Matrix.reindexAlgEquiv_apply] using
      kwOrderedSplitInternalBlock_reindex_eq_transition
        G order weight phase
  obtain ⟨n, hn⟩ := kwGraphTransition_isNilpotent_of_isAcyclic
    (kwOrderedPortInternalGraph G order)
    (kwOrderedPortInternalGraph_isAcyclic G order) weight
    (kwOrderedInternalPhase G order phase)
  refine ⟨n, ?_⟩
  apply A.injective
  rw [map_pow, hAB, hn, map_zero]


theorem kwOrderedSplit_det_eq_effective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order)
      weight phase
    let R := kwOrderedSplitTransitionInBlocks G order M
    ∃ n : ℕ,
      (1 - M).det =
        (1 - kwEliminateAcyclicInternal R.toBlocks₁₁ R.toBlocks₁₂
          R.toBlocks₂₁ R.toBlocks₂₂ n).det := by
  classical
  dsimp only
  let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order)
    weight phase
  let R := kwOrderedSplitTransitionInBlocks G order M
  obtain ⟨n, hn⟩ := kwOrderedSplitInternalBlock_isNilpotent
    G order weight phase
  refine ⟨n, ?_⟩
  have hnR : R.toBlocks₂₂ ^ n = 0 := by
    exact hn
  have hsub : kwOrderedSplitTransitionInBlocks G order (1 - M) = 1 - R := by
    ext i j
    simp [kwOrderedSplitTransitionInBlocks, Matrix.reindex_apply,
      Matrix.one_apply, R]
  calc
    (1 - M).det =
        (kwOrderedSplitTransitionInBlocks G order (1 - M)).det :=
      (kwOrderedSplitTransitionInBlocks_det G order (1 - M)).symm
    _ = (1 - R).det := by rw [hsub]
    _ = (1 - Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂).det := by
      rw [Matrix.fromBlocks_toBlocks]
    _ = (1 - kwEliminateAcyclicInternal R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n).det :=
      kw_det_eliminateAcyclicInternal R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n hnR


theorem kwOrderedSplit_externalBlock_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    (kwOrderedSplitTransitionInBlocks G order
      (kwGraphTransition (kwOrderedDartPortSplitGraph G order)
        weight phase)).toBlocks₁₁ = 0 := by
  ext d e
  unfold Matrix.toBlocks₁₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.zero_apply,
    Matrix.of_apply]
  split
  · rename_i hstep
    exfalso
    rcases hstep with ⟨hconsecutive, hne⟩
    simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
      kwOrderedExternalSplitDartOfDart_fst,
      kwOrderedExternalSplitDartOfDart_snd] at hconsecutive hne
    have hdart : e = d.symm := by
      have h := congrArg (kwDartOfPort G) hconsecutive
      simpa using h.symm
    subst e
    apply hne
    simp [SimpleGraph.Dart.edge]
  · rfl


theorem kwOrderedSplit_det_eq_pathEffective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 (KWDartPort G) → ℂ)
    (phase : (kwOrderedDartPortSplitGraph G order).Dart →
      (kwOrderedDartPortSplitGraph G order).Dart → ℂ) :
    let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order)
      weight phase
    let R := kwOrderedSplitTransitionInBlocks G order M
    ∃ n : ℕ,
      (1 - M).det =
        (1 - R.toBlocks₁₂ *
          kwNilpotentResolvent R.toBlocks₂₂ n * R.toBlocks₂₁).det := by
  classical
  dsimp only
  let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order)
    weight phase
  let R := kwOrderedSplitTransitionInBlocks G order M
  obtain ⟨n, hn⟩ := kwOrderedSplit_det_eq_effective G order weight phase
  refine ⟨n, ?_⟩
  rw [hn]
  unfold kwEliminateAcyclicInternal
  have hzero : R.toBlocks₁₁ = 0 := by
    exact kwOrderedSplit_externalBlock_eq_zero G order weight phase
  rw [hzero, zero_add]


end StatMech.FrontierA
