/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part4


namespace StatMech.FrontierA

open SimpleGraph

@[simp] theorem triangularTorusSplitEmbedWalk_support
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u v) :
    (triangularTorusSplitEmbedWalk L p).support =
      p.support.map (triangularTorusSplitEmbedVertex L) := by
  exact SimpleGraph.Walk.support_map _ _

@[simp] theorem triangularTorusSplitEmbedWalk_edges
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u v) :
    (triangularTorusSplitEmbedWalk L p).edges =
      p.edges.map (Sym2.map (triangularTorusSplitEmbedHom L)) := by
  exact SimpleGraph.Walk.edges_map _ _


theorem triangularTorusSplitEmbedWalk_isCycle
    (L : Nat) [Fact (2 < L)]
    {u : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u u)
    (hp : p.IsCycle) :
    (triangularTorusSplitEmbedWalk L p).IsCycle := by
  exact hp.map (triangularTorusSplitEmbedVertex_injective L)


theorem triangularTorusSplitEmbedWalk_verts_disjoint
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u u)
    (q : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk v v)
    (hdisjoint : Disjoint p.toSubgraph.verts q.toSubgraph.verts) :
    Disjoint (triangularTorusSplitEmbedWalk L p).toSubgraph.verts
      (triangularTorusSplitEmbedWalk L q).toSubgraph.verts := by
  apply Set.disjoint_left.mpr
  intro z hzp hzq
  have hzp' : z ∈ (triangularTorusSplitEmbedWalk L p).support :=
    (SimpleGraph.Walk.mem_verts_toSubgraph _).mp hzp
  have hzq' : z ∈ (triangularTorusSplitEmbedWalk L q).support :=
    (SimpleGraph.Walk.mem_verts_toSubgraph _).mp hzq
  rw [triangularTorusSplitEmbedWalk_support, List.mem_map] at hzp' hzq'
  rcases hzp' with ⟨x, hx, rfl⟩
  rcases hzq' with ⟨y, hy, hxy⟩
  have : x = y := triangularTorusSplitEmbedVertex_injective L hxy.symm
  subst y
  exact Set.disjoint_left.1 hdisjoint
    ((SimpleGraph.Walk.mem_verts_toSubgraph _).mpr hx)
    ((SimpleGraph.Walk.mem_verts_toSubgraph _).mpr hy)

end StatMech.FrontierA
