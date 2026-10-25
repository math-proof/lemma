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
import Def.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


@[simp] theorem latticeMinusOrbit_adj (K : Set (Site 2)) (e : Dart) (x y : Site 2) :
    (latticeMinusOrbit K e).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ ¬ IsOrbitEdge K e x y := Iff.rfl


theorem obs_orbitEdge_isBoundaryDart (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2} (h : IsOrbitEdge K e x y) :
    ∃ d : Dart, IsBoundaryDart K d ∧ SameOrbit K e d ∧
      ((d.tail = x ∧ d.head = y) ∨ (d.tail = y ∧ d.head = x)) := by
  obtain ⟨d, hd, hcase⟩ := h
  obtain ⟨n, hn⟩ := hd
  have hbd : IsBoundaryDart K d := by rw [← hn]; exact iterate_isBoundaryDart' K e he n
  exact ⟨d, hbd, ⟨n, hn⟩, hcase⟩


theorem obs_orbitEdge_one_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : (x ∈ K ↔ y ∉ K) := by
  obtain ⟨d, hbd, _, hcase⟩ := obs_orbitEdge_isBoundaryDart K e he h
  rcases hcase with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · subst ht hh; exact ⟨fun _ => hbd.2, fun _ => hbd.1⟩
  · subst ht hh; exact ⟨fun hx => absurd hx hbd.2, fun hy => absurd hbd.1 hy⟩


theorem obs_not_orbitEdge_of_both_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (hx : x ∈ K) (hy : y ∈ K) : ¬ IsOrbitEdge K e x y := fun h =>
  (obs_orbitEdge_one_in_K K e he h).mp hx hy


theorem obs_not_orbitEdge_of_both_not_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (hx : x ∉ K) (hy : y ∉ K) : ¬ IsOrbitEdge K e x y := fun h => by
  have hiff := obs_orbitEdge_one_in_K K e he h
  exact hy (by by_contra hyk; exact hx (hiff.mpr hyk))


theorem obs_orbitReachable_of_complReachable (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K)
    (h : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩) :
    (latticeMinusOrbit K e).Reachable u w := by
  obtain ⟨p⟩ := h
  suffices H : ∀ (a b : ↥(Kᶜ : Set (Site 2))), ((hypercubicLattice 2).induce Kᶜ).Walk a b →
      (latticeMinusOrbit K e).Reachable (a : Site 2) (b : Site 2) from H ⟨u, hu⟩ ⟨w, hw⟩ p
  intro a b q
  induction q with
  | nil => exact Reachable.refl _
  | @cons a b c hadj q' ih =>
    have hadj' : (hypercubicLattice 2).Adj (a : Site 2) (b : Site 2) := hadj
    have hno : ¬ IsOrbitEdge K e (a : Site 2) (b : Site 2) :=
      obs_not_orbitEdge_of_both_not_in_K K e he a.2 b.2
    exact (SimpleGraph.Adj.reachable ((latticeMinusOrbit_adj K e _ _).mpr ⟨hadj', hno⟩)).trans ih


theorem obs_orbitReachable_of_connected (o : Site 2) (e : Dart)
    (he : IsBoundaryDart (cluster 2 ω o) e) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hxy : Connected 2 ω x y) :
    (latticeMinusOrbit (cluster 2 ω o) e).Reachable x y := by
  obtain ⟨p⟩ := hxy
  suffices H : ∀ (a b : Site 2), (openSubgraph 2 ω).Walk a b → a ∈ cluster 2 ω o →
      (latticeMinusOrbit (cluster 2 ω o) e).Reachable a b from H x y p hx
  intro a b q
  induction q with
  | nil => intro _; exact Reachable.refl _
  | @cons a b c hadj q' ih =>
    intro ha
    have hadjL : (hypercubicLattice 2).Adj a b := hadj.1
    have hab_open : Connected 2 ω a b := ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩
    have hb : b ∈ cluster 2 ω o := by rw [mem_cluster] at ha ⊢; exact ha.trans hab_open
    have hno : ¬ IsOrbitEdge (cluster 2 ω o) e a b :=
      obs_not_orbitEdge_of_both_in_K (cluster 2 ω o) e he ha hb
    exact
      (SimpleGraph.Adj.reachable ((latticeMinusOrbit_adj _ e _ _).mpr ⟨hadjL, hno⟩)).trans (ih hb)


theorem obs_sameOrbit_of_orbitEdge_boundary (K : Set (Site 2)) (e f : Dart)
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f)
    (h : IsOrbitEdge K e f.tail f.head) : SameOrbit K e f := by
  obtain ⟨d, hbd, hso, hcase⟩ := obs_orbitEdge_isBoundaryDart K e he h
  rcases hcase with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have heq : d = f := Dart.ext ht hh
    rwa [heq] at hso
  · exfalso
    have hdtail : d.tail ∈ K := hbd.1
    rw [ht] at hdtail
    exact hf.2 hdtail


end Lattice
end StatMech
