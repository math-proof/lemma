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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part17
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwAngularSplitPhase_external_internal_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) e.1.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) e.1.snd) :
    kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 e.1 =
      -Complex.I * (kwPortAngleRoot embedding e.1.fst)⁻¹ := by
  unfold kwAngularSplitPhase
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd, kwDartOfPort_portOfDart]
  simp [e.2, hrank]

@[simp] theorem kwAngularSplitPhase_external_internal_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart)
    (e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) e.1.snd <
      kwOrderedPortRank (kwAngularPortOrder embedding) e.1.fst) :
    kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 e.1 =
      Complex.I * (kwPortAngleRoot embedding e.1.fst)⁻¹ := by
  unfold kwAngularSplitPhase
  simp only [kwOrderedExternalSplitDartOfDart_fst,
    kwOrderedExternalSplitDartOfDart_snd, kwDartOfPort_portOfDart]
  simp [e.2, not_lt_of_ge (le_of_lt hrank)]

@[simp] theorem kwAngularSplitPhase_internal_external
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding))
    (e : G.Dart) :
    kwAngularSplitPhase embedding d.1
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) e).1 =
      kwPortAngleRoot embedding (kwPortOfDart G e) := by
  unfold kwAngularSplitPhase
  simp [d.2]

@[simp] theorem kwAngularSplitPhase_internal_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)) :
    kwAngularSplitPhase embedding d.1 e.1 = 1 := by
  unfold kwAngularSplitPhase
  simp [d.2, e.2]


theorem kwAngularSplitPhase_endpointProduct_of_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G d.symm) <
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e))
    (first last : KWOrderedInternalSplitDart G
      (kwAngularPortOrder embedding))
    (hfirst : first.1.fst = kwPortOfDart G d.symm)
    (hfirstRank : kwOrderedPortRank (kwAngularPortOrder embedding)
        first.1.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) first.1.snd) :
    kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 first.1 *
      kwAngularSplitPhase embedding last.1
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) e).1 =
      embedding.turnPhase d e := by
  rw [kwAngularSplitPhase_external_internal_of_rank_lt
      embedding d first hfirstRank,
    kwAngularSplitPhase_internal_external]
  rw [embedding.turnPhase_eq_portRoots_of_rank_lt d e hde hrank]
  simp only [hfirst]


theorem kwAngularSplitPhase_endpointProduct_of_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart)
    (hde : d.snd = e.fst)
    (hrank : kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G e) <
      kwOrderedPortRank (kwAngularPortOrder embedding)
        (kwPortOfDart G d.symm))
    (first last : KWOrderedInternalSplitDart G
      (kwAngularPortOrder embedding))
    (hfirst : first.1.fst = kwPortOfDart G d.symm)
    (hfirstRank : kwOrderedPortRank (kwAngularPortOrder embedding)
        first.1.snd <
      kwOrderedPortRank (kwAngularPortOrder embedding) first.1.fst) :
    kwAngularSplitPhase embedding
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) d).1 first.1 *
      kwAngularSplitPhase embedding last.1
        (kwOrderedExternalSplitDartOfDart G
          (kwAngularPortOrder embedding) e).1 =
      embedding.turnPhase d e := by
  rw [kwAngularSplitPhase_external_internal_of_rank_gt
      embedding d first hfirstRank,
    kwAngularSplitPhase_internal_external]
  rw [embedding.turnPhase_eq_portRoots_of_rank_gt d e hde hrank]
  simp only [hfirst]


theorem kwAngularSplit_internalPhase_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    kwOrderedInternalPhase G (kwAngularPortOrder embedding)
        (kwAngularSplitPhase embedding) = fun _ _ ↦ 1 := by
  funext d e
  unfold kwOrderedInternalPhase
  exact kwAngularSplitPhase_internal_internal embedding
    ((kwOrderedInternalSplitDartEquiv G
      (kwAngularPortOrder embedding)).symm d)
    ((kwOrderedInternalSplitDartEquiv G
      (kwAngularPortOrder embedding)).symm e)

theorem kwDartPort_eq_of_fst_of_orderRank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) {p q : KWDartPort G}
    (hfst : p.1 = q.1)
    (hidx : kwOrderedPortRank order p = kwOrderedPortRank order q) :
    p = q := by
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  dsimp only at hfst hidx
  subst w
  have hij : order v i = order v j := Fin.ext hidx
  have : i = j := (order v).injective hij
  subst j
  rfl


end StatMech.FrontierA
