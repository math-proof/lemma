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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part24
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwAngularInternalExitSolution_of_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart)
    (hfaces : KWOrderedInternalDartFacesPort
      (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
    kwAngularInternalExitSolution embedding d e =
      kwPortAngleRoot embedding (kwPortOfDart G e) := by
  unfold kwAngularInternalExitSolution
  rw [if_pos hfaces]

theorem kwAngularInternalExitSolution_of_not_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart)
    (hfaces : ¬KWOrderedInternalDartFacesPort
      (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
    kwAngularInternalExitSolution embedding d e = 0 := by
  unfold kwAngularInternalExitSolution
  rw [if_neg hfaces]


theorem kwAngularSplit_internal_mul_exitSolution_of_faces_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart)
    (hfaces : KWOrderedInternalDartFacesPort
      (kwAngularPortOrder embedding) d (kwPortOfDart G e))
    (hne : d.1.snd ≠ kwPortOfDart G e) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ *
      kwAngularInternalExitSolution embedding) d e =
      kwPortAngleRoot embedding (kwPortOfDart G e) := by
  classical
  rw [Matrix.mul_apply]
  have hddata := kwOrderedInternalSplitDart_adj_data G
    (kwAngularPortOrder embedding) d
  have hrankne : kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd ≠
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e) := by
    intro hrank
    apply hne
    exact kwDartPort_eq_of_fst_of_orderRank
      (kwAngularPortOrder embedding) hfaces.1 hrank
  rcases hfaces.2 with ⟨hdinc, hdtarget⟩ | ⟨hddec, hdtarget⟩
  · have htarget : kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd <
        kwOrderedPortRank (kwAngularPortOrder embedding)
          (kwPortOfDart G e) := by omega
    have hqcard := ((kwAngularPortOrder embedding)
      (kwPortOfDart G e).1 (kwPortOfDart G e).2).isLt
    change kwOrderedPortRank (kwAngularPortOrder embedding)
      (kwPortOfDart G e) <
        Fintype.card (KWOutgoingDart (G := G) (kwPortOfDart G e).1) at hqcard
    have hcardeq :
        Fintype.card (KWOutgoingDart (G := G) d.1.snd.1) =
          Fintype.card (KWOutgoingDart (G := G) (kwPortOfDart G e).1) :=
      congrArg (fun v ↦ Fintype.card (KWOutgoingDart (G := G) v)) hfaces.1
    have hbound : kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd + 1 <
        Fintype.card (KWOutgoingDart (G := G) d.1.snd.1) := by omega
    let next := kwOrderedIncreasingInternalDartFrom G
      (kwAngularPortOrder embedding) d.1.snd hbound
    have hstep : KWOrderedInternalDartStep G
        (kwAngularPortOrder embedding) d next :=
      kwOrderedInternalDartStep_increasingFrom G
        (kwAngularPortOrder embedding) d hdinc hbound
    have hnextfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) next (kwPortOfDart G e) :=
      kwOrderedInternalDartFacesPort_step G
        (kwAngularPortOrder embedding) hstep
        ⟨hfaces.1, Or.inl ⟨hdinc, hdtarget⟩⟩ hne
    calc
      ∑ f, (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d f *
          kwAngularInternalExitSolution embedding f e =
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d next *
            kwAngularInternalExitSolution embedding next e := by
        apply Fintype.sum_eq_single next
        intro f hfn
        by_cases hs : KWOrderedInternalDartStep G
            (kwAngularPortOrder embedding) d f
        · have hnf := kwOrderedInternalDartStep_rightUnique G
            (kwAngularPortOrder embedding) hstep hs
          exact (hfn hnf.symm).elim
        · rw [kwAngularSplitBlocks_internal_apply_of_not_step
            embedding weight d f hs, zero_mul]
      _ = kwPortAngleRoot embedding (kwPortOfDart G e) := by
        rw [kwAngularSplitBlocks_internal_apply_of_step
            embedding weight d next hstep, one_mul,
          kwAngularInternalExitSolution_of_faces
            embedding next e hnextfaces]
  · have htarget : kwOrderedPortRank (kwAngularPortOrder embedding)
          (kwPortOfDart G e) <
        kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd := by omega
    have hbound : 0 <
        kwOrderedPortRank (kwAngularPortOrder embedding) d.1.snd := by omega
    let next := kwOrderedDecreasingInternalDartFrom G
      (kwAngularPortOrder embedding) d.1.snd hbound
    have hstep : KWOrderedInternalDartStep G
        (kwAngularPortOrder embedding) d next :=
      kwOrderedInternalDartStep_decreasingFrom G
        (kwAngularPortOrder embedding) d hddec hbound
    have hnextfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) next (kwPortOfDart G e) :=
      kwOrderedInternalDartFacesPort_step G
        (kwAngularPortOrder embedding) hstep
        ⟨hfaces.1, Or.inr ⟨hddec, hdtarget⟩⟩ hne
    calc
      ∑ f, (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d f *
          kwAngularInternalExitSolution embedding f e =
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d next *
            kwAngularInternalExitSolution embedding next e := by
        apply Fintype.sum_eq_single next
        intro f hfn
        by_cases hs : KWOrderedInternalDartStep G
            (kwAngularPortOrder embedding) d f
        · have hnf := kwOrderedInternalDartStep_rightUnique G
            (kwAngularPortOrder embedding) hstep hs
          exact (hfn hnf.symm).elim
        · rw [kwAngularSplitBlocks_internal_apply_of_not_step
            embedding weight d f hs, zero_mul]
      _ = kwPortAngleRoot embedding (kwPortOfDart G e) := by
        rw [kwAngularSplitBlocks_internal_apply_of_step
            embedding weight d next hstep, one_mul,
          kwAngularInternalExitSolution_of_faces
            embedding next e hnextfaces]


theorem kwAngularSplit_internal_mul_exitSolution_of_snd_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) (hsnd : d.1.snd = kwPortOfDart G e) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ *
      kwAngularInternalExitSolution embedding) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  by_cases hstep : KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d f
  · have hnot : ¬KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) f (kwPortOfDart G e) := by
      intro hfaces
      apply kwOrderedInternalDartStep_not_faces_snd G
        (kwAngularPortOrder embedding) hstep
      rwa [hsnd]
    rw [kwAngularSplitBlocks_internal_apply_of_step
        embedding weight d f hstep, one_mul,
      kwAngularInternalExitSolution_of_not_faces embedding f e hnot]
  · rw [kwAngularSplitBlocks_internal_apply_of_not_step
        embedding weight d f hstep, zero_mul]


theorem kwAngularSplit_internal_mul_exitSolution_of_not_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart)
    (hfaces : ¬KWOrderedInternalDartFacesPort
      (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ *
      kwAngularInternalExitSolution embedding) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  by_cases hstep : KWOrderedInternalDartStep G
      (kwAngularPortOrder embedding) d f
  · have hfnot : ¬KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) f (kwPortOfDart G e) := by
      intro hffaces
      apply hfaces
      exact kwOrderedInternalDartFacesPort_of_step G
        (kwAngularPortOrder embedding) hstep hffaces
    rw [kwAngularSplitBlocks_internal_apply_of_step
        embedding weight d f hstep, one_mul,
      kwAngularInternalExitSolution_of_not_faces embedding f e hfnot]
  · rw [kwAngularSplitBlocks_internal_apply_of_not_step
        embedding weight d f hstep, zero_mul]


theorem kwAngularSplit_exitSolution_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ) :
    (1 - (kwAngularSplitBlocks embedding weight).toBlocks₂₂) *
        kwAngularInternalExitSolution embedding =
      (kwAngularSplitBlocks embedding weight).toBlocks₂₁ := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  ext d e
  by_cases hsnd : d.1.snd = kwPortOfDart G e
  · have hfaces := kwOrderedInternalDartFacesPort_of_snd_eq G
      (kwAngularPortOrder embedding) d (kwPortOfDart G e) hsnd
    rw [Matrix.sub_apply,
      kwAngularInternalExitSolution_of_faces embedding d e hfaces,
      kwAngularSplit_internal_mul_exitSolution_of_snd_eq
        embedding weight d e hsnd,
      kwAngularSplitBlocks_exit_apply_of_connect
        embedding weight d e hsnd,
      sub_zero]
  · by_cases hfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) d (kwPortOfDart G e)
    · rw [Matrix.sub_apply,
        kwAngularInternalExitSolution_of_faces embedding d e hfaces,
        kwAngularSplit_internal_mul_exitSolution_of_faces_of_ne
          embedding weight d e hfaces hsnd,
        kwAngularSplitBlocks_exit_apply_of_not_connect
          embedding weight d e hsnd,
        sub_self]
    · rw [Matrix.sub_apply,
        kwAngularInternalExitSolution_of_not_faces embedding d e hfaces,
        kwAngularSplit_internal_mul_exitSolution_of_not_faces
          embedding weight d e hfaces,
        kwAngularSplitBlocks_exit_apply_of_not_connect
          embedding weight d e hsnd,
        sub_zero]


theorem kwAngularSplit_resolvent_mul_exit_eq_solution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (n : ℕ)
    (hpow : (kwAngularSplitBlocks embedding weight).toBlocks₂₂ ^ n = 0) :
    kwNilpotentResolvent
        (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
        (kwAngularSplitBlocks embedding weight).toBlocks₂₁ =
      kwAngularInternalExitSolution embedding := by
  calc
    kwNilpotentResolvent
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
          (kwAngularSplitBlocks embedding weight).toBlocks₂₁ =
        kwNilpotentResolvent
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
          ((1 - (kwAngularSplitBlocks embedding weight).toBlocks₂₂) *
            kwAngularInternalExitSolution embedding) := by
      rw [kwAngularSplit_exitSolution_equation embedding weight]
    _ = (kwNilpotentResolvent
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
          (1 - (kwAngularSplitBlocks embedding weight).toBlocks₂₂)) *
          kwAngularInternalExitSolution embedding := by
      rw [Matrix.mul_assoc]
    _ = kwAngularInternalExitSolution embedding := by
      rw [kwNilpotentResolvent_mul _ n hpow, Matrix.one_mul]


theorem kwAngularSplit_enter_mul_exitSolution_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : G.Dart) (hde : d.snd = e.fst) (hnb : d.edge ≠ e.edge) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₁₂ *
      kwAngularInternalExitSolution embedding) d e =
      weight d.edge * embedding.turnPhase d e := by
  classical
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  have hpfirst : p.1 = d.snd := by
    have h := kwDartOfPort_fst G p
    simpa [p] using h.symm
  have hqfirst : q.1 = e.fst := by
    have h := kwDartOfPort_fst G q
    simpa [q] using h.symm
  have hpqfirst : p.1 = q.1 := hpfirst.trans (hde.trans hqfirst.symm)
  have hpq : p ≠ q := by
    intro hpq
    have hdart := congrArg (kwDartOfPort G) hpq
    apply hnb
    have heq : d.symm = e := by simpa [p, q] using hdart
    rw [← heq]
    exact d.edge_symm.symm
  have hrankne : kwOrderedPortRank (kwAngularPortOrder embedding) p ≠
      kwOrderedPortRank (kwAngularPortOrder embedding) q := by
    intro hrank
    exact hpq (kwDartPort_eq_of_fst_of_orderRank
      (kwAngularPortOrder embedding) hpqfirst hrank)
  rw [Matrix.mul_apply]
  rcases lt_or_gt_of_ne hrankne with hrank | hrank
  · have hqcard := ((kwAngularPortOrder embedding) q.1 q.2).isLt
    change kwOrderedPortRank (kwAngularPortOrder embedding) q <
      Fintype.card (KWOutgoingDart (G := G) q.1) at hqcard
    have hcardeq : Fintype.card (KWOutgoingDart (G := G) p.1) =
        Fintype.card (KWOutgoingDart (G := G) q.1) :=
      congrArg (fun v ↦ Fintype.card (KWOutgoingDart (G := G) v)) hpqfirst
    have hbound : kwOrderedPortRank (kwAngularPortOrder embedding) p + 1 <
        Fintype.card (KWOutgoingDart (G := G) p.1) := by omega
    let first := kwOrderedIncreasingInternalDartFrom G
      (kwAngularPortOrder embedding) p hbound
    have hfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) first q :=
      kwOrderedIncreasingInternalDartFrom_faces G
        (kwAngularPortOrder embedding) p q hpqfirst hrank hbound
    have hconnect : p = first.1.fst := by simp [first]
    calc
      ∑ f, (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d f *
          kwAngularInternalExitSolution embedding f e =
          (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d first *
            kwAngularInternalExitSolution embedding first e := by
        apply Fintype.sum_eq_single first
        intro f hne
        by_cases hfconnect : p = f.1.fst
        · by_cases hffaces : KWOrderedInternalDartFacesPort
              (kwAngularPortOrder embedding) f q
          · have hffirst := kwOrderedInternalDart_eq_of_fst_eq_of_faces G
                (kwAngularPortOrder embedding)
                (hfconnect.symm.trans hconnect) hffaces hfaces
            exact (hne hffirst).elim
          · rw [kwAngularInternalExitSolution_of_not_faces
                embedding f e (by simpa [q] using hffaces), mul_zero]
        · rw [kwAngularSplitBlocks_enter_apply_of_not_connect
              embedding weight d f (by simpa [p] using hfconnect), zero_mul]
      _ = weight d.edge * embedding.turnPhase d e := by
        rw [kwAngularSplitBlocks_enter_apply_of_connect
            embedding weight d first (by simpa [p] using hconnect),
          kwAngularInternalExitSolution_of_faces
            embedding first e (by simpa [q] using hfaces)]
        have hphase := kwAngularSplitPhase_endpointProduct_of_rank_lt
          embedding d e hde (by simpa [p, q] using hrank) first first
          (by simpa [p] using hconnect.symm)
          (by simp [first])
        rw [kwAngularSplitPhase_internal_external] at hphase
        rw [← hphase]
        ring
  · have hbound : 0 <
        kwOrderedPortRank (kwAngularPortOrder embedding) p := by omega
    let first := kwOrderedDecreasingInternalDartFrom G
      (kwAngularPortOrder embedding) p hbound
    have hfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) first q :=
      kwOrderedDecreasingInternalDartFrom_faces G
        (kwAngularPortOrder embedding) p q hpqfirst hrank hbound
    have hconnect : p = first.1.fst := by simp [first]
    calc
      ∑ f, (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d f *
          kwAngularInternalExitSolution embedding f e =
          (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d first *
            kwAngularInternalExitSolution embedding first e := by
        apply Fintype.sum_eq_single first
        intro f hne
        by_cases hfconnect : p = f.1.fst
        · by_cases hffaces : KWOrderedInternalDartFacesPort
              (kwAngularPortOrder embedding) f q
          · have hffirst := kwOrderedInternalDart_eq_of_fst_eq_of_faces G
                (kwAngularPortOrder embedding)
                (hfconnect.symm.trans hconnect) hffaces hfaces
            exact (hne hffirst).elim
          · rw [kwAngularInternalExitSolution_of_not_faces
                embedding f e (by simpa [q] using hffaces), mul_zero]
        · rw [kwAngularSplitBlocks_enter_apply_of_not_connect
              embedding weight d f (by simpa [p] using hfconnect), zero_mul]
      _ = weight d.edge * embedding.turnPhase d e := by
        rw [kwAngularSplitBlocks_enter_apply_of_connect
            embedding weight d first (by simpa [p] using hconnect),
          kwAngularInternalExitSolution_of_faces
            embedding first e (by simpa [q] using hfaces)]
        have hphase := kwAngularSplitPhase_endpointProduct_of_rank_gt
          embedding d e hde (by simpa [p, q] using hrank) first first
          (by simpa [p] using hconnect.symm)
          (by
            have hs := kwOrderedDecreasingInternalDartFrom_rank_snd G
              (kwAngularPortOrder embedding) p hbound
            change kwOrderedPortRank (kwAngularPortOrder embedding) first.1.snd <
              kwOrderedPortRank (kwAngularPortOrder embedding) first.1.fst
            simp only [first, kwOrderedDecreasingInternalDartFrom_fst]
            omega)
        rw [kwAngularSplitPhase_internal_external] at hphase
        rw [← hphase]
        ring


theorem kwAngularSplit_enter_mul_exitSolution_of_not_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (d e : G.Dart) (hstep : ¬(d.snd = e.fst ∧ d.edge ≠ e.edge)) :
    ((kwAngularSplitBlocks embedding weight).toBlocks₁₂ *
      kwAngularInternalExitSolution embedding) d e = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro f _
  let p := kwPortOfDart G d.symm
  let q := kwPortOfDart G e
  by_cases hconnect : p = f.1.fst
  · by_cases hfaces : KWOrderedInternalDartFacesPort
        (kwAngularPortOrder embedding) f q
    · exfalso
      apply hstep
      have hpfirst : p.1 = d.snd := by
        have h := kwDartOfPort_fst G p
        simpa [p] using h.symm
      have hqfirst : q.1 = e.fst := by
        have h := kwDartOfPort_fst G q
        simpa [q] using h.symm
      have hfdata := kwOrderedInternalSplitDart_adj_data G
        (kwAngularPortOrder embedding) f
      have hde : d.snd = e.fst := by
        rw [← hpfirst, ← hqfirst, hconnect]
        exact hfdata.1.trans hfaces.1
      refine ⟨hde, ?_⟩
      intro hedge
      rw [SimpleGraph.dart_edge_eq_iff] at hedge
      rcases hedge with hedge | hedge
      · rw [hedge] at hde
        exact e.fst_ne_snd hde.symm
      · have hpq : p = q := by
          apply kwDartOfPort_injective G
          simp [p, q, hedge]
        apply kwOrderedInternalDart_not_faces_fst G
          (kwAngularPortOrder embedding) f
        have htarget : q = f.1.fst := hpq.symm.trans hconnect
        rwa [← htarget]
    · rw [kwAngularInternalExitSolution_of_not_faces
          embedding f e (by simpa [q] using hfaces), mul_zero]
  · rw [kwAngularSplitBlocks_enter_apply_of_not_connect
        embedding weight d f (by simpa [p] using hconnect), zero_mul]


theorem kwAngularSplit_enter_mul_exitSolution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ) :
    (kwAngularSplitBlocks embedding weight).toBlocks₁₂ *
        kwAngularInternalExitSolution embedding =
      kwGraphTransition G weight embedding.turnPhase := by
  ext d e
  unfold kwGraphTransition
  by_cases hstep : d.snd = e.fst ∧ d.edge ≠ e.edge
  · rw [if_pos hstep,
      kwAngularSplit_enter_mul_exitSolution_of_step
        embedding weight d e hstep.1 hstep.2]
  · rw [if_neg hstep,
      kwAngularSplit_enter_mul_exitSolution_of_not_step
        embedding weight d e hstep]


theorem kwAngularSplit_pathEffective_eq_original
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ)
    (n : ℕ)
    (hpow : (kwAngularSplitBlocks embedding weight).toBlocks₂₂ ^ n = 0) :
    (kwAngularSplitBlocks embedding weight).toBlocks₁₂ *
        kwNilpotentResolvent
          (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n *
        (kwAngularSplitBlocks embedding weight).toBlocks₂₁ =
      kwGraphTransition G weight embedding.turnPhase := by
  rw [Matrix.mul_assoc,
    kwAngularSplit_resolvent_mul_exit_eq_solution
      embedding weight n hpow,
    kwAngularSplit_enter_mul_exitSolution]


theorem kwAngularSplit_det_eq_original
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)).det =
      (1 - kwGraphTransition G weight embedding.turnPhase).det := by
  classical
  let M := kwGraphTransition
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)
  let R := kwAngularSplitBlocks embedding weight
  obtain ⟨n, hn⟩ := kwOrderedSplitInternalBlock_isNilpotent G
    (kwAngularPortOrder embedding) (kwOrderedSplitWeight G weight)
    (kwAngularSplitPhase embedding)
  change R.toBlocks₂₂ ^ n = 0 at hn
  have hzero : R.toBlocks₁₁ = 0 := by
    exact kwOrderedSplit_externalBlock_eq_zero G
      (kwAngularPortOrder embedding) (kwOrderedSplitWeight G weight)
      (kwAngularSplitPhase embedding)
  have hpath : R.toBlocks₁₂ * kwNilpotentResolvent R.toBlocks₂₂ n *
      R.toBlocks₂₁ = kwGraphTransition G weight embedding.turnPhase := by
    exact kwAngularSplit_pathEffective_eq_original embedding weight n hn
  have hsub : kwOrderedSplitTransitionInBlocks G
      (kwAngularPortOrder embedding) (1 - M) = 1 - R := by
    ext i j
    simp [kwOrderedSplitTransitionInBlocks, Matrix.reindex_apply,
      Matrix.one_apply, R, M, kwAngularSplitBlocks]
  change (1 - M).det = (1 - kwGraphTransition G weight embedding.turnPhase).det
  calc
    (1 - M).det =
        (kwOrderedSplitTransitionInBlocks G
          (kwAngularPortOrder embedding) (1 - M)).det :=
      (kwOrderedSplitTransitionInBlocks_det G
        (kwAngularPortOrder embedding) (1 - M)).symm
    _ = (1 - R).det := by rw [hsub]
    _ = (1 - Matrix.fromBlocks R.toBlocks₁₁ R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂).det := by
      rw [Matrix.fromBlocks_toBlocks]
    _ = (1 - kwInternalGadgetTransition 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂).det := by
      rw [hzero]
      rfl
    _ = (1 - kwEliminateAcyclicInternal 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n).det :=
      kw_det_eliminateAcyclicInternal 0 R.toBlocks₁₂
        R.toBlocks₂₁ R.toBlocks₂₂ n hn
    _ = (1 - kwGraphTransition G weight embedding.turnPhase).det := by
      unfold kwEliminateAcyclicInternal
      rw [zero_add, hpath]


theorem kwOrderedDartPortSplitGraph_degree_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) :
    (kwOrderedDartPortSplitGraph G order).degree p ≤ 3 := by
  classical
  let code : (kwOrderedDartPortSplitGraph G order).neighborSet p →
      Fin 3 := fun q ↦
    if kwDartOfPort G q.1 = (kwDartOfPort G p).symm then 0
    else if kwOrderedPortRank order q.1 + 1 =
        kwOrderedPortRank order p then 1
    else 2
  have hcode : Function.Injective code := by
    intro q r hqr
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    simp only [code] at hqr
    rw [SimpleGraph.mem_neighborSet,
      kwOrderedDartPortSplitGraph_adj] at hq hr
    by_cases hqext : kwDartOfPort G q = (kwDartOfPort G p).symm
    · have hrext : kwDartOfPort G r = (kwDartOfPort G p).symm := by
        by_contra hne
        simp only [hqext, ↓reduceIte, hne] at hqr
        split at hqr <;> omega
      apply Subtype.ext
      exact kwDartOfPort_injective G (hqext.trans hrext.symm)
    · by_cases hrext : kwDartOfPort G r = (kwDartOfPort G p).symm
      · simp only [hqext, hrext, ↓reduceIte] at hqr
        split at hqr <;> omega
      · have hqdata := hq.resolve_left hqext
        have hrdata := hr.resolve_left hrext
        by_cases hqpred : kwOrderedPortRank order q + 1 =
            kwOrderedPortRank order p
        · have hrpred : kwOrderedPortRank order r + 1 =
              kwOrderedPortRank order p := by
            by_contra hne
            simp [hqext, hrext, hqpred, hne] at hqr
          apply Subtype.ext
          apply kwDartPort_eq_of_fst_of_orderRank order
              (hqdata.1.symm.trans hrdata.1)
          omega
        · have hrpred : ¬(kwOrderedPortRank order r + 1 =
              kwOrderedPortRank order p) := by
            intro hp
            simp [hqext, hrext, hqpred, hp] at hqr
          have hqsucc : kwOrderedPortRank order p + 1 =
              kwOrderedPortRank order q := hqdata.2.resolve_right hqpred
          have hrsucc : kwOrderedPortRank order p + 1 =
              kwOrderedPortRank order r := hrdata.2.resolve_right hrpred
          apply Subtype.ext
          apply kwDartPort_eq_of_fst_of_orderRank order
              (hqdata.1.symm.trans hrdata.1)
          omega
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective code hcode

theorem kwOrderedDartPortSplitGraph_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    kwOrderedDartPortSplitGraph G (kwIdentityPortOrder G) =
      kwDartPortSplitGraph G := by
  ext p q
  rfl


end StatMech.FrontierA
