/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Instance.StatisticalMechanics.Code.Ising.KWGeometricDual.Part5
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_componentBoundaryGraph_degree (P : PlanarZ2Subgraph) (C : kwg_Face P)
    (x : P.V) :
    (kwg_componentBoundaryGraph P C).degree x =
      jce_degree
        (jed_cutSet (fun z =>
          (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)) (P.emb x) := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : SimpleGraph.LocallyFinite (kwg_componentBoundaryGraph P C) := fun _ =>
    Fintype.ofFinite _
  let E := jed_cutSet (fun z =>
    (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)
  rw [← jed_degree_primalGraph E (P.emb x)]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => P.emb y)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact ⟨P.isSub hy.1, hy.2⟩
  · intro y _ z _ h
    exact P.emb.injective h
  · intro z hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    have hzimg : (imageGraph P).Adj (P.emb x) z := by
      have hcut : s(P.emb x, z) ∈ E := hz.2
      have himg := kwg_componentCut_subset_imageGraph P C hcut
      rwa [SimpleGraph.mem_edgeSet] at himg
    obtain ⟨a, b, hab, ha, hb⟩ := (imageGraph_adj P (P.emb x) z).mp hzimg
    have hax : a = x := P.emb.injective (ha.trans rfl)
    subst a
    refine ⟨b, ?_, hb⟩
    rw [SimpleGraph.mem_neighborFinset]
    refine ⟨hab, ?_⟩
    change s(P.emb x, P.emb b) ∈ E
    rw [hb]
    exact hz.2


theorem kwg_componentBoundaryGraph_even (P : PlanarZ2Subgraph) (C : kwg_Face P)
    (x : P.V) : Even ((kwg_componentBoundaryGraph P C).degree x) := by
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : SimpleGraph.LocallyFinite (kwg_componentBoundaryGraph P C) := fun _ =>
    Fintype.ofFinite _
  rw [kwg_componentBoundaryGraph_degree P C x]
  exact kwg_componentCut_even P C (P.emb x)


end Ising
end StatMech
