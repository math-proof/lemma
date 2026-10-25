/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingFacts
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem icb_orbitReached_straight_step (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d)
    (hfront : d.head + (-rot90Fun d.dir) ∉ K)
    (hside : d.tail + (-rot90Fun d.dir) ∈ K) :
    OrbitReached K e (d.head + (-rot90Fun d.dir)) := by
  refine ⟨dartNext K d, dartNext_isBoundaryDart K d hd, ?_, ?_⟩
  · exact dartNext_straight_head K d hfront hside
  · obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩


theorem icb_orbitReached_corner_step (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d)
    (hfront : d.head + (-rot90Fun d.dir) ∉ K)
    (hside : d.tail + (-rot90Fun d.dir) ∉ K) :
    OrbitReached K e (d.tail + (-rot90Fun d.dir)) := by
  refine ⟨dartNext K d, dartNext_isBoundaryDart K d hd, ?_, ?_⟩
  · exact dartNext_left_head K d hfront hside
  · obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩


theorem icb_orbitReached_wallStep (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d) :
    OrbitReached K e (dartNext K d).head ∧
      ((dartNext K d).head = d.head ∨ KingAdj d.head (dartNext K d).head) := by
  refine ⟨⟨dartNext K d, dartNext_isBoundaryDart K d hd, rfl, ?_⟩,
    kf_dartNext_head_kingAdj_or_eq K d⟩
  obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩


end Lattice
end StatMech
