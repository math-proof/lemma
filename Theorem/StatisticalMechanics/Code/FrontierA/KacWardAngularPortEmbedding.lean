/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortExternal


namespace StatMech.FrontierA

open Set SimpleGraph

theorem KWAngularPortRadiusData.external_original_edge_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart}
    (hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm)
    (he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm)
    (hedge : d.edge ≠ e.edge) :
    (kwDartOfPort G d.fst).edge ≠ (kwDartOfPort G e.fst).edge := by
  intro horig
  apply hedge
  rw [SimpleGraph.dart_edge_eq_iff] at horig
  rcases horig with hsame | hrev
  · have hfst : d.fst = e.fst := (kwDartOfPort_injective G) hsame
    have hsnd : d.snd = e.snd := by
      apply kwDartOfPort_injective G
      rw [hd, he, hsame]
    have hde : d = e := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext hfst hsnd
    rw [hde]
  · have hfst : d.fst = e.snd := by
      apply kwDartOfPort_injective G
      rw [he, hrev]
    have hsnd : d.snd = e.fst := by
      apply kwDartOfPort_injective G
      rw [hd, hrev]
      simp
    have hde : d = e.symm := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext hfst hsnd
    rw [hde]
    exact e.edge_symm

theorem KWAngularPortRadiusData.internalChords_disjoint_same_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart}
    (hd : ¬kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm)
    (he : ¬kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm)
    (howner : d.fst.1 = e.fst.1)
    (hedge : d.edge ≠ e.edge) :
    Disjoint
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) d.fst) z
        (kwAngularPortVertex embedding (data.radius : ℝ) d.snd)}
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) e.fst) z
        (kwAngularPortVertex embedding (data.radius : ℝ) e.snd)} := by
  have dd := (kwOrderedDartPortSplitGraph_adj G
    (kwAngularPortOrder embedding) d.fst d.snd).mp d.adj |>.resolve_left hd
  have ed := (kwOrderedDartPortSplitGraph_adj G
    (kwAngularPortOrder embedding) e.fst e.snd).mp e.adj |>.resolve_left he
  have hdOwner : d.fst.1 = d.snd.1 := dd.1
  have heOwner : e.fst.1 = e.snd.1 := ed.1
  let rank := kwOrderedPortRank (kwAngularPortOrder embedding)
  rcases dd.2 with hdinc | hddec
  · rcases ed.2 with heinc | hedec
    · exact data.internalChords_disjoint_of_same_owner
        hdOwner howner (howner.trans heOwner)
        hdinc heinc hedge
    · have h := data.internalChords_disjoint_of_same_owner
        hdOwner (howner.trans heOwner) howner
        hdinc hedec (by
          simpa only [SimpleGraph.Dart.edge, Sym2.eq_swap] using hedge)
      rw [Set.disjoint_left]
      intro z hzd hze
      exact Set.disjoint_left.mp h hzd ((sbtw_comm).mpr hze)
  · rcases ed.2 with heinc | hedec
    · have h := data.internalChords_disjoint_of_same_owner
        hdOwner.symm (hdOwner.symm.trans howner)
        (hdOwner.symm.trans (howner.trans heOwner))
        hddec heinc (by
          simpa only [SimpleGraph.Dart.edge, Sym2.eq_swap] using hedge)
      rw [Set.disjoint_left]
      intro z hzd hze
      exact Set.disjoint_left.mp h ((sbtw_comm).mpr hzd) hze
    · have h := data.internalChords_disjoint_of_same_owner
        hdOwner.symm (hdOwner.symm.trans (howner.trans heOwner))
        (hdOwner.symm.trans howner)
        hddec hedec (by
          simpa only [SimpleGraph.Dart.edge, Sym2.eq_swap] using hedge)
      rw [Set.disjoint_left]
      intro z hzd hze
      exact Set.disjoint_left.mp h
        ((sbtw_comm).mpr hzd) ((sbtw_comm).mpr hze)

theorem KWAngularPortRadiusData.internal_external_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart}
    (hd : ¬kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm)
    (he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm) :
    Disjoint
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) d.fst) z
        (kwAngularPortVertex embedding (data.radius : ℝ) d.snd)}
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) e.fst) z
        (kwAngularPortVertex embedding (data.radius : ℝ) e.snd)} := by
  have dd := (kwOrderedDartPortSplitGraph_adj G
    (kwAngularPortOrder embedding) d.fst d.snd).mp d.adj |>.resolve_left hd
  have hdne : d.fst ≠ d.snd := d.fst_ne_snd
  let a := kwDartOfPort G e.fst
  rw [Set.disjoint_left]
  intro z hzd hze
  have hzball := data.internalChord_mem_ball dd.1 hdne hzd
  have hzeOrig := data.matching_sbtw_original he hze
  by_cases hvfst : d.fst.1 = a.fst
  · have hout := data.radius_lt_dist_fst_of_matching_sbtw he hze
    have hin := Metric.mem_ball'.mp hzball
    rw [hvfst] at hin
    linarith
  by_cases hvsnd : d.fst.1 = a.snd
  · have hout := data.radius_lt_dist_snd_of_matching_sbtw he hze
    have hin := Metric.mem_ball'.mp hzball
    rw [hvsnd] at hin
    linarith
  have hsep := data.vertex_edge_separated d.fst.1 a hvfst hvsnd z
    (mem_segment_iff_wbtw.mpr hzeOrig.1)
  have hin := Metric.mem_ball'.mp hzball
  linarith

theorem KWAngularPortRadiusData.port_not_between_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart}
    (hd : ¬kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm)
    (v : KWDartPort G) (hvfst : v ≠ d.fst) (hvsnd : v ≠ d.snd) :
    ¬Sbtw ℝ
      (kwAngularPortVertex embedding (data.radius : ℝ) d.fst)
      (kwAngularPortVertex embedding (data.radius : ℝ) v)
      (kwAngularPortVertex embedding (data.radius : ℝ) d.snd) := by
  intro hv
  have dd := (kwOrderedDartPortSplitGraph_adj G
    (kwAngularPortOrder embedding) d.fst d.snd).mp d.adj |>.resolve_left hd
  have hball := data.internalChord_mem_ball dd.1 d.fst_ne_snd hv
  by_cases howner : v.1 = d.fst.1
  · have hsphere := data.portVertex_mem_sphere v
    have hlt := Metric.mem_ball'.mp hball
    have heq : dist (kwAngularPortVertex embedding (data.radius : ℝ) v)
        (embedding.vertex d.fst.1) = (data.radius : ℝ) := by
      rw [← howner]
      exact hsphere
    rw [_root_.dist_comm] at hlt
    linarith
  · have hsep := data.vertex_separated d.fst.1 v.1 (Ne.symm howner)
    have hin := Metric.mem_ball'.mp hball
    have hvdist : dist (kwAngularPortVertex embedding (data.radius : ℝ) v)
        (embedding.vertex v.1) = (data.radius : ℝ) := by
      exact data.portVertex_mem_sphere v
    have htri : dist (embedding.vertex d.fst.1) (embedding.vertex v.1) ≤
        dist (embedding.vertex d.fst.1)
            (kwAngularPortVertex embedding (data.radius : ℝ) v) +
          dist (kwAngularPortVertex embedding (data.radius : ℝ) v)
            (embedding.vertex v.1) := dist_triangle _ _ _
    rw [hvdist] at htri
    linarith

theorem KWAngularPortRadiusData.port_not_between_external
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart}
    (hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm)
    (v : KWDartPort G) (hvfst : v ≠ d.fst) (hvsnd : v ≠ d.snd) :
    ¬Sbtw ℝ
      (kwAngularPortVertex embedding (data.radius : ℝ) d.fst)
      (kwAngularPortVertex embedding (data.radius : ℝ) v)
      (kwAngularPortVertex embedding (data.radius : ℝ) d.snd) := by
  intro hv
  let a := kwDartOfPort G d.fst
  have hvOrig := data.matching_sbtw_original hd hv
  by_cases hvfstOwner : v.1 = a.fst
  · have hout := data.radius_lt_dist_fst_of_matching_sbtw hd hv
    have heq : dist (embedding.vertex a.fst)
        (kwAngularPortVertex embedding (data.radius : ℝ) v) =
        (data.radius : ℝ) := by
      rw [← hvfstOwner]
      simpa only [_root_.dist_comm] using data.portVertex_mem_sphere v
    linarith
  by_cases hvsndOwner : v.1 = a.snd
  · have hout := data.radius_lt_dist_snd_of_matching_sbtw hd hv
    have heq : dist (embedding.vertex a.snd)
        (kwAngularPortVertex embedding (data.radius : ℝ) v) =
        (data.radius : ℝ) := by
      rw [← hvsndOwner]
      simpa only [_root_.dist_comm] using data.portVertex_mem_sphere v
    linarith
  have hsep := data.vertex_edge_separated v.1 a hvfstOwner hvsndOwner
    (kwAngularPortVertex embedding (data.radius : ℝ) v)
    (mem_segment_iff_wbtw.mpr hvOrig.1)
  have heq : dist (embedding.vertex v.1)
      (kwAngularPortVertex embedding (data.radius : ℝ) v) =
      (data.radius : ℝ) := by
    simpa only [_root_.dist_comm] using data.portVertex_mem_sphere v
  linarith


end StatMech.FrontierA
