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
import Instance.StatisticalMechanics.Code.Ising.KWGeometricDual.Part4
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


@[simp] theorem kwg_incidentMod2_mk {V : Type*} (v x y : V) :
    kwg_incidentMod2 v s(x, y) ↔
      (x = v ∧ y ≠ v) ∨ (y = v ∧ x ≠ v) := Iff.rfl


theorem kwg_incident_iff_componentCut (P : PlanarZ2Subgraph) (e : kwg_Edge P)
    (C : kwg_Face P) :
    kwg_incidentMod2 C (kwg_dualEnds P e) ↔
      kwg_embeddedEdge P e ∈ jed_cutSet
        (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C) := by
  rw [← kwg_flanks_shared P e]
  rw [jed_mem_cutSet_iff _ (kwg_flanks_adj P e)]
  unfold kwg_dualEnds
  rw [kwg_incidentMod2_mk]
  tauto


theorem kwg_componentCut_subset_imageGraph (P : PlanarZ2Subgraph) (C : kwg_Face P) :
    jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C) ⊆
      (imageGraph P).edgeSet := by
  rintro _ ⟨a, b, hab, rfl, hsplit⟩
  by_contra hn
  have hw : (whb_faceRegion (imageGraph P)).Adj a b := ⟨hab, hn⟩
  have heq := ConnectedComponent.connectedComponentMk_eq_of_adj hw
  change ((whb_faceRegion (imageGraph P)).connectedComponentMk a = C ↔
    ¬ (whb_faceRegion (imageGraph P)).connectedComponentMk b = C) at hsplit
  rw [heq] at hsplit
  tauto


theorem kwg_componentCut_even (P : PlanarZ2Subgraph) (C : kwg_Face P) (v : Site 2) :
    Even (jce_degree
      (jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)) v) :=
  jed_cutSet_even _ v


end Ising
end StatMech
