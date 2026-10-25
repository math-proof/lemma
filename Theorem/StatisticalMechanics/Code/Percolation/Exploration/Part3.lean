/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.Exploration.Part3
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


theorem mem_incidentWithin {K S : Set (Site d)} {x y : Site d} (hx : x ∈ K) (hy : y ∈ S) :
    s(x, y) ∈ incidentWithin K S := ⟨x, hx, y, hy, rfl⟩


theorem agree_KS {K S : Set (Site d)} {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
    {x y : Site d} (hx : x ∈ K) (hy : y ∈ S) :
    ω s(x, y) = ω' s(x, y) :=
  hagree _ (mem_incidentWithin hx hy)


theorem isOpenEdge_transfer {K S : Set (Site d)} {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
    {x y : Site d} (hx : x ∈ K) (hy : y ∈ S)
    (h : IsOpenEdge d ω x y) : IsOpenEdge d ω' x y := by
  obtain ⟨hadj, hopen⟩ := h
  exact ⟨hadj, by rw [← agree_KS hagree hx hy]; exact hopen⟩


theorem clusterWithin_closed {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    {x y : Site d} (hx : x ∈ clusterWithin d ω S o)
    (hyS : y ∈ S) (hopen : IsOpenEdge d ω x y) :
    y ∈ clusterWithin d ω S o := by
  obtain ⟨hxS, hoS, hconn⟩ := hx
  exact ⟨hyS, hoS, hconn.trans (SimpleGraph.Adj.reachable (show IsOpenEdge d ω x y from hopen))⟩


theorem walk_transfer {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
    {a b : ↥S} (w : (openSubgraphInduce d ω S).Walk a b)
    (ha : (a : Site d) ∈ clusterWithin d ω S o) :
    (b : Site d) ∈ clusterWithin d ω S o ∧
      Nonempty ((openSubgraphInduce d ω' S).Walk a b) := by
  induction w with
  | nil => exact ⟨ha, ⟨SimpleGraph.Walk.nil⟩⟩
  | @cons u v t hadj p ih =>
    have hopen : IsOpenEdge d ω (u : Site d) (v : Site d) := hadj
    have hvK : (v : Site d) ∈ clusterWithin d ω S o := clusterWithin_closed ha v.2 hopen
    obtain ⟨hbK, ⟨w'⟩⟩ := ih hvK
    have hopen' : IsOpenEdge d ω' (u : Site d) (v : Site d) :=
      isOpenEdge_transfer hagree ha v.2 hopen
    exact ⟨hbK, ⟨SimpleGraph.Walk.cons (show (openSubgraphInduce d ω' S).Adj u v from hopen') w'⟩⟩


theorem K_closed_omega' {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
    {x y : Site d} (hxK : x ∈ clusterWithin d ω S o) (hyS : y ∈ S)
    (hopen' : IsOpenEdge d ω' x y) : y ∈ clusterWithin d ω S o := by
  have hopen : IsOpenEdge d ω x y := by
    obtain ⟨hadj, ho'⟩ := hopen'
    exact ⟨hadj, by rw [agree_KS hagree hxK hyS]; exact ho'⟩
  exact clusterWithin_closed hxK hyS hopen


theorem walk_trap_omega' {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
    {a b : ↥S} (w : (openSubgraphInduce d ω' S).Walk a b)
    (ha : (a : Site d) ∈ clusterWithin d ω S o) :
    (b : Site d) ∈ clusterWithin d ω S o := by
  induction w with
  | nil => exact ha
  | @cons u v t hadj p ih =>
    have hopen' : IsOpenEdge d ω' (u : Site d) (v : Site d) := hadj
    exact ih (K_closed_omega' hagree ha v.2 hopen')


theorem clusterWithin_congr {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    (hoS : o ∈ S)
    (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e) :
    clusterWithin d ω' S o = clusterWithin d ω S o := by
  have hoK : o ∈ clusterWithin d ω S o :=
    ⟨hoS, hoS, connectedWithin_refl ω S ⟨o, hoS⟩⟩
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro y ⟨_, _, hconn'⟩
    obtain ⟨w⟩ := hconn'
    exact walk_trap_omega' hagree w hoK
  · rintro y ⟨hyS, hoS', hconn⟩
    obtain ⟨w⟩ := hconn
    obtain ⟨_, ⟨w'⟩⟩ := walk_transfer hagree w hoK
    exact ⟨hyS, hoS', ⟨w'⟩⟩


end Percolation
end StatMech
