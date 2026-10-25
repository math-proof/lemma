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
import Def.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part3
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem exitOrbitFaceLoop_length_pos (hfin : (cluster 2 ω (origin 2)).Finite) :
    0 < (exitOrbitFaceLoop (ω := ω) hfin).length := by
  rw [exitOrbitFaceLoop, SimpleGraph.Walk.length_copy]
  exact dartOrbitFaceLoop_length_pos _ _ _ _


theorem orbitEdges_subset_bdBarrier (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    ∀ ⦃f g : Site 2⦄, s(f, g) ∈ (dartOrbitFaceLoop K hK e he).edges →
      bdEdge K (sharedPrimalEdge f g) :=
  fun _ _ h => dartOrbitFaceLoop_edges_bdEdge K hK e he h


theorem orbit_separates_origin (_hfin : (cluster 2 ω (origin 2)).Finite) {z : Site 2}
    (hz : z ∉ cluster 2 ω (origin 2)) :
    ¬ (latticeMinusBarrier (cluster 2 ω (origin 2))).Reachable (origin 2) z :=
  cluster_separated_from_exterior (origin 2) hz


theorem orbit_origin_crossCount_odd (_hfin : (cluster 2 ω (origin 2)).Finite) {z : Site 2}
    (hz : z ∉ cluster 2 ω (origin 2)) (w : (hypercubicLattice 2).Walk (origin 2) z) :
    ¬ Even (crossCount (cluster 2 ω (origin 2)) w) :=
  origin_crossCount_odd (origin 2) hz w


theorem iterate_eq_mod_of_period {α : Type*} (f : α → α) (x : α) {p : ℕ}
    (hp : f^[p] x = x) (n : ℕ) : f^[n] x = f^[n % p] x := by
  have hper : Function.IsPeriodicPt f p x := hp
  conv_lhs => rw [← Nat.mod_add_div n p, Function.iterate_add_apply]
  rw [(hper.mul_const (n / p)).eq]


theorem dartFace_iterate_mem_dartOrbitFaceLoop_support (K : Set (Site 2)) (hK : K.Finite)
    (e : Dart) (he : IsBoundaryDart K e) (n : ℕ) :
    dartFace ((dartNext K)^[n] e) ∈ (dartOrbitFaceLoop K hK e he).support := by
  classical
  set p := (dartNext_periodic K hK e he).choose with hp
  have hpspec := (dartNext_periodic K hK e he).choose_spec
  have hpper : (dartNext K)^[p] e = e := hpspec.2
  have hppos : 0 < p := hpspec.1
  
  have heq : (dartNext K)^[n] e = (dartNext K)^[n % p] e :=
    iterate_eq_mod_of_period (dartNext K) e hpper n
  have hlt : n % p ≤ p := le_of_lt (Nat.mod_lt _ hppos)
  rw [heq]
  
  rw [dartOrbitFaceLoop, SimpleGraph.Walk.support_copy]
  exact dartFace_iterate_mem_dartOrbitFaceWalk_support K e he hlt


theorem exitOrbitFaceLoop_mem_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    leftExitFaceDown (ω := ω) hfin ∈ (exitOrbitFaceLoop (ω := ω) hfin).support := by
  classical
  obtain ⟨n, hn⟩ := h
  
  have hface : dartFace ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin))
      = leftExitFaceDown (ω := ω) hfin := by
    rw [hn]; exact dartFace_leftExitDart (ω := ω) hfin
  
  have hmem := dartFace_iterate_mem_dartOrbitFaceLoop_support (cluster 2 ω (origin 2)) hfin
    (exitDart (ω := ω) hfin) (exitDart_isBoundaryDart (ω := ω) hfin) n
  rw [hface] at hmem
  
  rw [exitOrbitFaceLoop, SimpleGraph.Walk.support_copy]
  exact hmem


theorem exitOrbitFaceLoop_exists_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    ∃ w ∈ (exitOrbitFaceLoop (ω := ω) hfin).support, w 0 ≤ 0 :=
  ⟨leftExitFaceDown (ω := ω) hfin, exitOrbitFaceLoop_mem_leftFace (ω := ω) hfin h,
    leftExitFaceDown_coord0_nonpos (ω := ω) hfin⟩


end Lattice
end StatMech
