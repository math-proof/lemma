/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortExternal
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding


namespace StatMech.FrontierA

open Set SimpleGraph

noncomputable def KWAngularPortRadiusData.toStraightLineEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) :
    KWStraightLineEmbedding
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) where
  vertex := kwAngularPortVertex embedding (data.radius : ℝ)
  vertex_injective := data.portVertex_injective
  vertex_not_strictly_between := by
    intro d v hvfst hvsnd
    by_cases hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
    · exact data.port_not_between_external hd v hvfst hvsnd
    · exact data.port_not_between_internal hd v hvfst hvsnd
  edgeInteriors_disjoint := by
    intro d e hedge
    by_cases hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
    · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
      · apply (embedding.edgeInteriors_disjoint
          (kwDartOfPort G d.fst) (kwDartOfPort G e.fst)
          (data.external_original_edge_ne hd he hedge)).mono
        · intro z hz
          exact data.matching_sbtw_original hd hz
        · intro z hz
          exact data.matching_sbtw_original he hz
      · exact (data.internal_external_disjoint he hd).symm
    · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
      · exact data.internal_external_disjoint hd he
      · have dd := (kwOrderedDartPortSplitGraph_adj G
          (kwAngularPortOrder embedding) d.fst d.snd).mp d.adj |>.resolve_left hd
        have ed := (kwOrderedDartPortSplitGraph_adj G
          (kwAngularPortOrder embedding) e.fst e.snd).mp e.adj |>.resolve_left he
        by_cases howner : d.fst.1 = e.fst.1
        · exact data.internalChords_disjoint_same_owner hd he howner hedge
        · exact data.internalChords_disjoint_of_owner_ne
            dd.1 d.fst_ne_snd ed.1 e.fst_ne_snd howner

end StatMech.FrontierA
