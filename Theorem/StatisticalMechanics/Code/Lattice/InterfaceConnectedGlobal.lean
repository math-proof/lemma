/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.KingFacts
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem ifg_dartNext_head_kingReachable (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (boundaryKingGraph K).Reachable
      ⟨e.head, he.2⟩ ⟨(dartNext K e).head, (dartNext_isBoundaryDart K e he).2⟩ := by
  rcases kf_dartNext_head_kingAdj_or_eq K e with hfix | hking
  · 
    have hsub : (⟨(dartNext K e).head, (dartNext_isBoundaryDart K e he).2⟩ : ↥(Kᶜ : Set (Site 2)))
        = ⟨e.head, he.2⟩ := Subtype.ext hfix
    rw [hsub]
  · 
    exact (((boundaryKingGraph_adj K _ _).mpr hking)).reachable


theorem ifg_iterate_head_kingReachable (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) :
    (boundaryKingGraph K).Reachable
      ⟨e.head, he.2⟩ ⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart' K e he n).2⟩ := by
  induction n with
  | zero => exact Reachable.refl _
  | succ m ih =>
    have hbd := iterate_isBoundaryDart' K e he m
    have hstep := ifg_dartNext_head_kingReachable K ((dartNext K)^[m] e) hbd
    have htrans := ih.trans hstep
    
    have hval : (dartNext K ((dartNext K)^[m] e)).head = ((dartNext K)^[m + 1] e).head := by
      rw [Function.iterate_succ_apply']
    have hsub :
        (⟨(dartNext K ((dartNext K)^[m] e)).head,
            (dartNext_isBoundaryDart K ((dartNext K)^[m] e) hbd).2⟩ : ↥(Kᶜ : Set (Site 2)))
          = ⟨((dartNext K)^[m + 1] e).head, (iterate_isBoundaryDart' K e he (m + 1)).2⟩ :=
      Subtype.ext hval
    rwa [hsub] at htrans


theorem ifg_orbit_kingReachable (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f) (h : SameOrbit K e f) :
    (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
  obtain ⟨n, hn⟩ := h
  have hr := ifg_iterate_head_kingReachable K e he n
  have hval : ((dartNext K)^[n] e).head = f.head := by rw [hn]
  have hsub : (⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart' K e he n).2⟩
      : ↥(Kᶜ : Set (Site 2))) = ⟨f.head, hf.2⟩ := Subtype.ext hval
  rwa [hsub] at hr


end Lattice
end StatMech
