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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part19
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedInternalDartFacesPort_of_snd_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) (q : KWDartPort G)
    (h : d.1.snd = q) : KWOrderedInternalDartFacesPort order d q := by
  have hd := kwOrderedInternalSplitDart_adj_data G order d
  have hrank := congrArg (kwOrderedPortRank order) h
  unfold KWOrderedInternalDartFacesPort
  constructor
  · exact congrArg Sigma.fst h
  · rcases hd.2 with hinc | hdec
    · left
      constructor <;> omega
    · right
      constructor <;> omega


theorem kwOrderedInternalDartFacesPort_of_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order} {q : KWDartPort G}
    (hstep : KWOrderedInternalDartStep G order d e)
    (heq : KWOrderedInternalDartFacesPort order e q) :
    KWOrderedInternalDartFacesPort order d q := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hsteprank := congrArg (kwOrderedPortRank order) hstep.1
  rcases heq with ⟨heqfst, heqdir⟩
  constructor
  · exact (congrArg Sigma.fst hstep.1).trans
      (hedata.1.trans heqfst)
  · rcases heqdir with ⟨heinc, hetarget⟩ | ⟨hedec, hetarget⟩
    · rcases hddata.2 with hdinc | hddec
      · left
        constructor <;> omega
      · have hdgt : kwOrderedPortRank order d.1.snd <
            kwOrderedPortRank order d.1.fst := by omega
        have := kwOrderedInternalDartStep_rank_gt G order hstep hdgt
        omega
    · rcases hddata.2 with hdinc | hddec
      · have hdlt : kwOrderedPortRank order d.1.fst <
            kwOrderedPortRank order d.1.snd := by omega
        have := kwOrderedInternalDartStep_rank_lt G order hstep hdlt
        omega
      · right
        constructor <;> omega


theorem kwOrderedInternalDartFacesPort_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order} {q : KWDartPort G}
    (hstep : KWOrderedInternalDartStep G order d e)
    (hdq : KWOrderedInternalDartFacesPort order d q)
    (hne : d.1.snd ≠ q) :
    KWOrderedInternalDartFacesPort order e q := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hsteprank := congrArg (kwOrderedPortRank order) hstep.1
  rcases hdq with ⟨hdqfst, hdqdir⟩
  have hrankne : kwOrderedPortRank order d.1.snd ≠
      kwOrderedPortRank order q := by
    intro hrank
    apply hne
    exact kwDartPort_eq_of_fst_of_orderRank order hdqfst hrank
  constructor
  · exact hedata.1.symm.trans
      ((congrArg Sigma.fst hstep.1).symm.trans hdqfst)
  · rcases hdqdir with ⟨hdinc, hdtarget⟩ | ⟨hddec, hdtarget⟩
    · have heinc := kwOrderedInternalDartStep_rank_lt
        G order hstep hdinc
      left
      constructor
      · exact heinc
      · rcases hedata.2 with heinc' | hedec' <;> omega
    · have hedec := kwOrderedInternalDartStep_rank_gt
        G order hstep hddec
      right
      constructor
      · exact hedec
      · rcases hedata.2 with heinc' | hedec' <;> omega


theorem kwOrderedInternalDartStep_not_faces_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order}
    (hstep : KWOrderedInternalDartStep G order d e) :
    ¬KWOrderedInternalDartFacesPort order e d.1.snd := by
  intro hfaces
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hsteprank := congrArg (kwOrderedPortRank order) hstep.1
  rcases hddata.2 with hdinc | hddec
  · have hdlt : kwOrderedPortRank order d.1.fst <
        kwOrderedPortRank order d.1.snd := by omega
    have helt := kwOrderedInternalDartStep_rank_lt G order hstep hdlt
    rcases hfaces.2 with ⟨heinc, htarget⟩ | ⟨hedec, htarget⟩
    · rcases hedata.2 with heinc' | hedec' <;> omega
    · omega
  · have hdgt : kwOrderedPortRank order d.1.snd <
        kwOrderedPortRank order d.1.fst := by omega
    have hegt := kwOrderedInternalDartStep_rank_gt G order hstep hdgt
    rcases hfaces.2 with ⟨heinc, htarget⟩ | ⟨hedec, htarget⟩
    · omega
    · rcases hedata.2 with heinc' | hedec' <;> omega

theorem kwOrderedInternalDart_not_faces_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) :
    ¬KWOrderedInternalDartFacesPort order d d.1.fst := by
  intro hfaces
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  rcases hfaces.2 with ⟨hinc, htarget⟩ | ⟨hdec, htarget⟩ <;>
    rcases hddata.2 with hdinc | hddec <;> omega


theorem kwOrderedInternalDart_eq_of_fst_eq_of_faces
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order} {q : KWDartPort G}
    (hfst : d.1.fst = e.1.fst)
    (hdq : KWOrderedInternalDartFacesPort order d q)
    (heq : KWOrderedInternalDartFacesPort order e q) : d = e := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hfstrank := congrArg (kwOrderedPortRank order) hfst
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact hfst
  · apply kwDartPort_eq_of_fst_of_orderRank order
    · exact hddata.1.symm.trans
        ((congrArg Sigma.fst hfst).trans hedata.1)
    · rcases hdq.2 with ⟨hdinc, hdtarget⟩ | ⟨hddec, hdtarget⟩ <;>
        rcases heq.2 with ⟨heinc, hetarget⟩ | ⟨hedec, hetarget⟩ <;>
        rcases hddata.2 with hdinc' | hddec' <;>
        rcases hedata.2 with heinc' | hedec' <;> omega


end StatMech.FrontierA
