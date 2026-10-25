/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitSeparatesProof.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem ofw_orbitEdge_one_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : (x ∈ K ↔ y ∉ K) :=
  obs_orbitEdge_one_in_K K e he h


theorem ofw_orbitEdge_bdEdge_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : bdEdge K s(x, y) :=
  osp_orbitEdge_bdEdge K e he h


theorem ofw_localConstancy_gives_support_only (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2} (hadj : (hypercubicLattice 2).Adj x y)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(x, y)) :
    x ∈ (olb_orbitLoop K hK e he).support ∨ y ∈ (olb_orbitLoop K hK e he).support :=
  olb_orbit_leftRegion_bdEdge K hK e he hadj hbd


theorem ofw_loopFaceEdge_not_orbitEdge (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {f g : Site 2} (hf : f ∉ K) (hg : g ∉ K) : ¬ IsOrbitEdge K e f g :=
  obs_not_orbitEdge_of_both_not_in_K K e he hf hg


end Lattice
end StatMech
