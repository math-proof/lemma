/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedBuild.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Def.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part4
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem obs_latticeMinusOrbit_le_barrier (K : Set (Site 2)) (e : Dart)
    (hcov : OrbitCoversBoundaryEdges K e) :
    latticeMinusOrbit K e ≤ latticeMinusBarrier K := by
  intro x y h
  obtain ⟨hadj, hno⟩ := h
  exact ⟨hadj, fun hbd => hno (hcov hadj hbd)⟩


theorem obs_orbitSeparates_of_coversBoundary (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e := by
  intro hreach
  have hbarrier : (latticeMinusBarrier K).Reachable e.tail e.head :=
    hreach.mono (obs_latticeMinusOrbit_le_barrier K e hcov)
  exact not_reachable_latticeMinusBarrier K he.1 he.2 hbarrier


theorem obs_orbitCoversBoundaryEdges_singleton (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    OrbitCoversBoundaryEdges ({c} : Set (Site 2)) e := by
  intro x y hadj hbd
  rw [bdEdge_mk] at hbd
  simp only [Set.mem_singleton_iff] at hbd
  by_cases hx : x = c
  · have hy : y ≠ c := by have := hbd.mp hx; simpa using this
    have hadjcy : (hypercubicLattice 2).Adj c y := by rw [← hx]; exact hadj
    refine ⟨⟨c, y, hadjcy⟩, ?_, Or.inl ⟨hx.symm, rfl⟩⟩
    exact ifc_singleton_sameOrbit c e ⟨c, y, hadjcy⟩ he
      ⟨Set.mem_singleton _, by simpa using hy⟩
  · have hy : y = c := by
      by_contra hyne
      exact hx (hbd.mpr hyne)
    have hadjcx : (hypercubicLattice 2).Adj c x := by rw [← hy]; exact hadj.symm
    refine ⟨⟨c, x, hadjcx⟩, ?_, Or.inr ⟨hy.symm, rfl⟩⟩
    exact ifc_singleton_sameOrbit c e ⟨c, x, hadjcx⟩ he
      ⟨Set.mem_singleton _, by simpa using hx⟩


theorem obs_orbitSeparates_singleton (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    OrbitSeparates ({c} : Set (Site 2)) e :=
  obs_orbitSeparates_of_coversBoundary ({c} : Set (Site 2)) e he
    (obs_orbitCoversBoundaryEdges_singleton c e he)


theorem obs_exitDartsSameOrbit_of_orbitSeparates (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω (origin 2)) e →
        OrbitSeparates (cluster 2 ω (origin 2)) e)
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ExitDartsSameOrbit ω hfin :=
  icb_exitDartsSameOrbit_of_traceSurjective (ω := ω) hfin
    (obs_traceSurjective_of_orbitSeparates (origin 2) hsep) R hR hr hl


theorem obs_pc_lt_one_of_orbitSeparates_and_links
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  pc_lt_one_via_dartOrbit h


end Lattice
end StatMech
