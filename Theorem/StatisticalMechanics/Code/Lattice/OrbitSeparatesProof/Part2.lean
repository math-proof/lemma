/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedBuild.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part4
import Def.StatisticalMechanics.Code.Lattice.OrbitSeparatesProof.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem osp_orbitSeparates_of_residues (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hF1 : OrbitWindsBdEdge K hK e he) (hF2 : OrbitFillsWinding K hK e he) :
    OrbitSeparates K e := by
  set S := osp_windingRegion K hK e he with hSdef
  intro hreach
  
  have hle : latticeMinusOrbit K e ≤ latticeMinusBarrier S := by
    intro x y h
    obtain ⟨hadj, hno⟩ := h
    exact ⟨hadj, fun hbd => hno (hF2 x y hadj hbd)⟩
  
  obtain ⟨w⟩ := hreach.mono hle
  
  have hsame : (e.tail ∈ S ↔ e.head ∈ S) := latticeMinusBarrier_sameSide S w
  
  have hF1' : (e.tail ∈ S ↔ e.head ∉ S) := by
    unfold OrbitWindsBdEdge at hF1; rw [← hSdef, bdEdge_mk] at hF1; exact hF1
  by_cases ht : e.tail ∈ S
  · exact (hF1'.mp ht) (hsame.mp ht)
  · have hh : ¬ (e.head ∉ S) := fun hno => ht (hF1'.mpr hno)
    push Not at hh
    exact ht (hsame.mpr hh)


theorem osp_orbitWindsBdEdge_iff (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    OrbitWindsBdEdge K hK e he ↔
      (e.tail ∈ osp_windingRegion K hK e he ↔ e.head ∉ osp_windingRegion K hK e he) := by
  unfold OrbitWindsBdEdge; rw [bdEdge_mk]


theorem osp_orbitEdge_bdEdge (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : bdEdge K s(x, y) := by
  rw [bdEdge_mk]; exact obs_orbitEdge_one_in_K K e he h


theorem osp_fillsWinding_endpoint_face (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2} (hadj : (hypercubicLattice 2).Adj x y)
    (hbd : bdEdge (osp_windingRegion K hK e he) s(x, y)) :
    x ∈ (olb_orbitLoop K hK e he).support ∨ y ∈ (olb_orbitLoop K hK e he).support :=
  olb_orbit_leftRegion_bdEdge K hK e he hadj hbd


theorem osp_singleton_orbitEdge_endpoint (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) {x y : Site 2}
    (h : IsOrbitEdge ({c} : Set (Site 2)) e x y) : x = c ∨ y = c := by
  obtain ⟨d, hbd, _hso, hcase⟩ := obs_orbitEdge_isBoundaryDart ({c} : Set (Site 2)) e he h
  have hdc : d.tail = c := by
    have : d.tail ∈ ({c} : Set (Site 2)) := hbd.1
    rwa [Set.mem_singleton_iff] at this
  rcases hcase with ⟨ht, _hh⟩ | ⟨ht, _hh⟩
  · left; rw [← ht]; exact hdc
  · right; rw [← ht]; exact hdc


theorem osp_singleton_posAxisEdge_isOrbitEdge (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    IsOrbitEdge ({c} : Set (Site 2)) e c (c + ![1, 0]) := by
  have hadj : (hypercubicLattice 2).Adj c (c + ![1, 0]) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hne : (c + ![1, 0] : Site 2) ≠ c := by
    intro hcon
    have : (c + ![1, 0] : Site 2) 0 = c 0 := by rw [hcon]
    simp at this
  set d : Dart := ⟨c, c + ![1, 0], hadj⟩ with hd
  have hdbd : IsBoundaryDart ({c} : Set (Site 2)) d :=
    ⟨Set.mem_singleton _, by rw [Set.mem_singleton_iff]; exact hne⟩
  exact ⟨d, ifc_singleton_sameOrbit c e d he hdbd, Or.inl ⟨rfl, rfl⟩⟩


theorem osp_singleton_orbitEdges_not_even_degree (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    IsOrbitEdge ({c} : Set (Site 2)) e c (c + ![1, 0]) ∧
      (∀ y : Site 2, IsOrbitEdge ({c} : Set (Site 2)) e (c + ![1, 0]) y → y = c) := by
  refine ⟨osp_singleton_posAxisEdge_isOrbitEdge c e he, ?_⟩
  intro y h
  rcases osp_singleton_orbitEdge_endpoint c e he h with h1 | h1
  · exfalso
    have : (c + ![1, 0] : Site 2) 0 = c 0 := by rw [h1]
    simp at this
  · exact h1


theorem osp_orbitWindsBdEdge_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
    OrbitWindsBdEdge K hK e he := by
  have hbdK : bdEdge K s(e.tail, e.head) := by
    rw [bdEdge_mk]; exact ⟨fun _ => he.2, fun _ => he.1⟩
  exact (hmatch s(e.tail, e.head)).mp hbdK


theorem osp_orbitFillsWinding_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he))
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitFillsWinding K hK e he := by
  intro x y hadj hbd
  have hbdK : bdEdge K s(x, y) := (hmatch s(x, y)).mpr hbd
  exact hcov hadj hbdK


theorem osp_orbitSeparates_of_match_cover (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he))
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e :=
  osp_orbitSeparates_of_residues K hK e he
    (osp_orbitWindsBdEdge_of_match K hK e he hmatch)
    (osp_orbitFillsWinding_of_match K hK e he hmatch hcov)


theorem osp_traceSurjective_of_residues (hfin : (cluster 2 ω (origin 2)).Finite)
    (hF1 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitWindsBdEdge (cluster 2 ω (origin 2)) hfin e he)
    (hF2 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitFillsWinding (cluster 2 ω (origin 2)) hfin e he) :
    OrbitTraceSurjective (cluster 2 ω (origin 2)) :=
  obs_traceSurjective_of_orbitSeparates (origin 2)
    (fun e he => osp_orbitSeparates_of_residues (cluster 2 ω (origin 2)) hfin e he (hF1 e he)
      (hF2 e he))


theorem osp_interfaceConnected_of_residues (hfin : (cluster 2 ω (origin 2)).Finite)
    (hF1 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitWindsBdEdge (cluster 2 ω (origin 2)) hfin e he)
    (hF2 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitFillsWinding (cluster 2 ω (origin 2)) hfin e he) :
    InterfaceConnected (cluster 2 ω (origin 2)) :=
  (orbitTraceSurjective_iff_interfaceConnected (cluster 2 ω (origin 2))).mp
    (osp_traceSurjective_of_residues (ω := ω) hfin hF1 hF2)


theorem osp_exitDartsSameOrbit_of_residues (hfin : (cluster 2 ω (origin 2)).Finite)
    (hF1 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitWindsBdEdge (cluster 2 ω (origin 2)) hfin e he)
    (hF2 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitFillsWinding (cluster 2 ω (origin 2)) hfin e he)
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ExitDartsSameOrbit ω hfin :=
  obs_exitDartsSameOrbit_of_orbitSeparates (ω := ω) hfin
    (fun e he => osp_orbitSeparates_of_residues (cluster 2 ω (origin 2)) hfin e he (hF1 e he)
      (hF2 e he)) R hR hr hl


theorem osp_pc_lt_one_of_residues_and_links
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  obs_pc_lt_one_of_orbitSeparates_and_links h


end Lattice
end StatMech
