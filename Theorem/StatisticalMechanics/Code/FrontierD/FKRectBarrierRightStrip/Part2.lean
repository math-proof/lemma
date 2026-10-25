/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectBarrierRightStrip


namespace StatMech.FrontierD

noncomputable section

theorem fkRect_inducedOpenGraph_eq_of_agreesOutside_disjoint
    (R : FKRectTorus) (S T : Set R.Vertex)
    (hdisj : ∀ v, v ∈ T → v ∉ S)
    (omega tau : R.Configuration)
    (hot : ∀ a : R.EdgeIndex,
      fkRectTorusIndexedEdge R a ∉
        Set.range (FK.ocd_innerEdge
          (Subtype.val : FKRectInducedVertex R S → R.Vertex)) →
      omega a = tau a) :
    (fkRectOpenGraph R omega).induce T =
      (fkRectOpenGraph R tau).induce T := by
  ext x y
  constructor
  · rintro ⟨a, hopen, ha⟩
    refine ⟨a, ?_, ha⟩
    rw [← hot a]
    · exact hopen
    · intro hrange
      have hxy := (fkRect_innerEdge_subtype_mk_mem_range_iff
        R S x.1 y.1).1 (by simpa only [ha] using hrange)
      exact hdisj x.1 x.2 hxy.1
  · rintro ⟨a, hopen, ha⟩
    refine ⟨a, ?_, ha⟩
    rw [hot a]
    · exact hopen
    · intro hrange
      have hxy := (fkRect_innerEdge_subtype_mk_mem_range_iff
        R S x.1 y.1).1 (by simpa only [ha] using hrange)
      exact hdisj x.1 x.2 hxy.1

theorem fkRectSetConnectionWithinEvent_dependsOnOutsideRegion
    (R : FKRectTorus) (S T X Y : Set R.Vertex)
    (hdisj : ∀ v, v ∈ T → v ∉ S) :
    FKRectDependsOnOutsideRegion R S
      (fkRectSetConnectionWithinEvent R T X Y) := by
  intro omega tau hot
  have hgraph := fkRect_inducedOpenGraph_eq_of_agreesOutside_disjoint
    R S T hdisj omega tau hot
  constructor
  · rintro ⟨x, hx, y, hy, hreach⟩
    exact ⟨x, hx, y, hy, by
      unfold FKRectConnectedWithin at hreach ⊢
      rwa [← hgraph]⟩
  · rintro ⟨x, hx, y, hy, hreach⟩
    exact ⟨x, hx, y, hy, by
      unfold FKRectConnectedWithin at hreach ⊢
      rwa [hgraph]⟩


end
end StatMech.FrontierD
