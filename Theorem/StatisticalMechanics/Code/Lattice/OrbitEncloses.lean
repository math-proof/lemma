/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.OrbitEncloses
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem dartOrbitFaceWalk_length (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) : (dartOrbitFaceWalk K e he n).length = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [dartOrbitFaceWalk, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_concat, ih]


theorem dartOrbitFaceWalk_support (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) : (dartOrbitFaceWalk K e he n).support
      = (List.range (n + 1)).map (fun k => dartFace ((dartNext K)^[k] e)) := by
  induction n with
  | zero => simp [dartOrbitFaceWalk]
  | succ m ih =>
    rw [dartOrbitFaceWalk, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, ih,
      List.range_succ (n := m + 1), List.map_append]
    simp [Function.iterate_succ_apply']


theorem dartFace_iterate_mem_dartOrbitFaceWalk_support (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) {n k : ℕ} (hk : k ≤ n) :
    dartFace ((dartNext K)^[k] e) ∈ (dartOrbitFaceWalk K e he n).support := by
  rw [dartOrbitFaceWalk_support]
  rw [List.mem_map]
  exact ⟨k, List.mem_range.mpr (by omega), rfl⟩


theorem dartOrbitFaceWalk_edges_bdEdge (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) {f g : Site 2} (h : s(f, g) ∈ (dartOrbitFaceWalk K e he n).edges) :
    bdEdge K (sharedPrimalEdge f g) := by
  have hadj : (faceBoundaryGraph K).Adj f g := (dartOrbitFaceWalk K e he n).adj_of_mem_edges h
  exact faceBoundaryGraph_sharedPrimalEdge_bdEdge K hadj


end Lattice
end StatMech
