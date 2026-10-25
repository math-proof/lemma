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
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part4
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


@[simp] theorem kwg_dualGraph_vertexSet (P : PlanarZ2Subgraph) :
    (kwg_dualGraph P).vertexSet = Set.univ := rfl

@[simp] theorem kwg_dualGraph_edgeSet (P : PlanarZ2Subgraph) :
    (kwg_dualGraph P).edgeSet = Set.univ := rfl

theorem kwg_dualGraph_isLink_iff (P : PlanarZ2Subgraph) (e : kwg_Edge P)
    (x y : kwg_Face P) :
    (kwg_dualGraph P).IsLink e x y ↔ kwg_dualEnds P e = s(x, y) := Iff.rfl


theorem kwg_unique_outerFace (P : PlanarZ2Subgraph) :
    ∃! C : kwg_Face P, C.supp.Infinite :=
  jfc_whb_unique_infinite_component P


theorem kwg_card_face_eq_faceCount (P : PlanarZ2Subgraph) :
    Nat.card (kwg_Face P) = faceCount P.G := by
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan P
  have hbounded :
      Nat.card {c : kwg_Face P // c.supp.Finite} = nullity P.G := by
    rw [Nat.card_congr e, Nat.card_fin]
  have hb : whc_faithfulRegionCount P = nullity P.G := by
    simpa only [whc_faithfulRegionCount] using hbounded
  have htotal := jfc_whb_bounded_add_one_eq_card P
  calc
    Nat.card (kwg_Face P) = whc_faithfulRegionCount P + 1 := htotal.symm
    _ = nullity P.G + 1 := congrArg (fun n => n + 1) hb
    _ = faceCount P.G := rfl


theorem kwg_card_edge_eq_ncard (P : PlanarZ2Subgraph) :
    Nat.card (kwg_Edge P) = P.G.edgeSet.ncard :=
  Nat.card_coe_set_eq P.G.edgeSet


end Ising
end StatMech
