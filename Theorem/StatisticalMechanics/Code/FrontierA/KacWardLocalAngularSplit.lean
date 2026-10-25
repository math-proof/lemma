/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Def.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwLocalAngularSplitPhase_external_internal_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hrank : kwOrderedPortRank (data.order) e.1.fst <
      kwOrderedPortRank (data.order) e.1.snd) :
    kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 e.1 =
      -Complex.I * (data.root e.1.fst)⁻¹ := by
  unfold kwLocalAngularSplitPhase
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd, kwDartOfPort_portOfDart]
  simp [e.2, hrank]

@[simp] theorem kwLocalAngularSplitPhase_external_internal_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hrank : kwOrderedPortRank (data.order) e.1.snd <
      kwOrderedPortRank (data.order) e.1.fst) :
    kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 e.1 =
      Complex.I * (data.root e.1.fst)⁻¹ := by
  unfold kwLocalAngularSplitPhase
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd, kwDartOfPort_portOfDart]
  simp [e.2, not_lt_of_ge (le_of_lt hrank)]

@[simp] theorem kwLocalAngularSplitPhase_internal_external
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) :
    kwLocalAngularSplitPhase data d.1
        (kwOrderedExternalSplitDartOfDart G
          (data.order) e).1 =
      data.root (kwPortOfDart G e) := by
  unfold kwLocalAngularSplitPhase
  simp [d.2]

@[simp] theorem kwLocalAngularSplitPhase_internal_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d e : KWOrderedInternalSplitDart G (data.order)) :
    kwLocalAngularSplitPhase data d.1 e.1 = 1 := by
  unfold kwLocalAngularSplitPhase
  simp [d.2, e.2]


theorem kwLocalAngularSplitPhase_endpointProduct_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (data.order)
        (kwPortOfDart G d.symm) <
      kwOrderedPortRank (data.order)
        (kwPortOfDart G e))
    (first last : KWOrderedInternalSplitDart G
      (data.order))
    (hfirst : first.1.fst = kwPortOfDart G d.symm)
    (hfirstRank : kwOrderedPortRank (data.order)
        first.1.fst <
      kwOrderedPortRank (data.order) first.1.snd) :
    kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 first.1 *
      kwLocalAngularSplitPhase data last.1
        (kwOrderedExternalSplitDartOfDart G
          (data.order) e).1 =
      data.phase d e := by
  rw [kwLocalAngularSplitPhase_external_internal_of_rank_lt
      data d first hfirstRank,
    kwLocalAngularSplitPhase_internal_external]
  rw [data.phase_eq_portRoots_of_rank_lt d e hde hrank]
  simp only [hfirst]


theorem kwLocalAngularSplitPhase_endpointProduct_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (data.order)
        (kwPortOfDart G e) <
      kwOrderedPortRank (data.order)
        (kwPortOfDart G d.symm))
    (first last : KWOrderedInternalSplitDart G
      (data.order))
    (hfirst : first.1.fst = kwPortOfDart G d.symm)
    (hfirstRank : kwOrderedPortRank (data.order)
        first.1.snd <
      kwOrderedPortRank (data.order) first.1.fst) :
    kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 first.1 *
      kwLocalAngularSplitPhase data last.1
        (kwOrderedExternalSplitDartOfDart G
          (data.order) e).1 =
      data.phase d e := by
  rw [kwLocalAngularSplitPhase_external_internal_of_rank_gt
      data d first hfirstRank,
    kwLocalAngularSplitPhase_internal_external]
  rw [data.phase_eq_portRoots_of_rank_gt d e hde hrank]
  simp only [hfirst]


theorem kwLocalAngularSplit_internalPhase_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) :
    kwOrderedInternalPhase G (data.order)
        (kwLocalAngularSplitPhase data) = fun _ _ ↦ 1 := by
  funext d e
  unfold kwOrderedInternalPhase
  exact kwLocalAngularSplitPhase_internal_internal data
    ((kwOrderedInternalSplitDartEquiv G
      (data.order)).symm d)
    ((kwOrderedInternalSplitDartEquiv G
      (data.order)).symm e)


theorem kwLocalAngularSplit_internalBlock_apply_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G
      (data.order))
    (hstep : KWOrderedInternalDartStep G
      (data.order) d e) :
    kwOrderedSplitInternalBlock G (data.order)
        (kwGraphTransition
          (kwOrderedDartPortSplitGraph G (data.order))
          (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)) d e =
      1 := by
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inr]
  change d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge at hstep
  rw [if_pos hstep,
    kwOrderedSplitWeight_internal G weight
      (data.order) d,
    kwLocalAngularSplitPhase_internal_internal]
  exact one_mul 1


theorem kwLocalAngularSplit_internalBlock_apply_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d e : KWOrderedInternalSplitDart G
      (data.order))
    (hstep : ¬KWOrderedInternalDartStep G
      (data.order) d e) :
    kwOrderedSplitInternalBlock G (data.order)
        (kwGraphTransition
          (kwOrderedDartPortSplitGraph G (data.order))
          (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)) d e =
      0 := by
  unfold kwOrderedSplitInternalBlock kwOrderedSplitTransitionInBlocks
    Matrix.toBlocks₂₂ kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  simp only [Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inr]
  change ¬(d.1.snd = e.1.fst ∧ d.1.edge ≠ e.1.edge) at hstep
  rw [if_neg hstep]


theorem kwLocalAngularSplit_enterBlock_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hconnect : kwPortOfDart G d.symm = e.1.fst) :
    (kwOrderedSplitTransitionInBlocks G (data.order)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwOrderedSplitWeight G weight)
        (kwLocalAngularSplitPhase data))).toBlocks₁₂ d e =
      weight d.edge * kwLocalAngularSplitPhase data
        (kwOrderedExternalSplitDartOfDart G
          (data.order) d).1 e.1 := by
  unfold Matrix.toBlocks₁₂ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_pos ⟨by simpa using hconnect, by
      exact kwOrderedExternalSplitDart_edge_ne_internal G
        (data.order) d e⟩,
    kwOrderedSplitWeight_matching]

theorem kwLocalAngularSplit_enterBlock_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (data.order))
    (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
    (kwOrderedSplitTransitionInBlocks G (data.order)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwOrderedSplitWeight G weight)
        (kwLocalAngularSplitPhase data))).toBlocks₁₂ d e = 0 := by
  unfold Matrix.toBlocks₁₂ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_neg (by
    intro h
    apply hconnect
    simpa using h.1)]


theorem kwLocalAngularSplit_exitBlock_apply_of_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hconnect : d.1.snd = kwPortOfDart G e) :
    (kwOrderedSplitTransitionInBlocks G (data.order)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwOrderedSplitWeight G weight)
        (kwLocalAngularSplitPhase data))).toBlocks₂₁ d e =
      data.root (kwPortOfDart G e) := by
  unfold Matrix.toBlocks₂₁ kwOrderedSplitTransitionInBlocks
    kwGraphTransition
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, kwOrderedSplitDartBlockEquiv_inl,
    kwOrderedSplitDartBlockEquiv_inr]
  rw [if_pos ⟨by simpa using hconnect,
      (kwOrderedExternalSplitDart_edge_ne_internal G
        (data.order) e d).symm⟩,
    kwOrderedSplitWeight_internal, kwLocalAngularSplitPhase_internal_external,
    one_mul]

theorem kwLocalAngularSplit_exitBlock_apply_of_not_connect
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (data.order))
    (e : G.Dart) (hconnect : d.1.snd ≠ kwPortOfDart G e) :
    (kwOrderedSplitTransitionInBlocks G (data.order)
      (kwGraphTransition
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwOrderedSplitWeight G weight)
        (kwLocalAngularSplitPhase data))).toBlocks₂₁ d e = 0 := by
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
