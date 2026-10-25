/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RosenfeldThroatClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EscapeThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossArcThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingPinchClose
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsCycleClose.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rtc_thickPoint_of_eastThroat {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
    (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
    (hDn : (![e, y - 1] : Site 2) ∈ Vc.support) :
    kns_ThickPoint Vc := by
  refine pcy_thickPoint_of_three_support_neighbors Vc hcyc hE
    (v₁ := (![e + 1, y] : Site 2)) (v₂ := (![e, y + 1] : Site 2)) (v₃ := (![e, y - 1] : Site 2))
    ?_ ?_ ?_ hSeed hUp hDn ?_ ?_ ?_
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  · intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  · intro h; have := congrFun h 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this; omega


theorem rtc_thickPoint_of_seedWall_nonConsec {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
    (hnon : s((![e, y] : Site 2), (![e + 1, y] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc :=
  gtp_thickPoint_of_adj_horiz Vc hE hSeed hnon


theorem rtc_thickPoint_of_upWall_nonConsec {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
    (hnon : s((![e, y] : Site 2), (![e, y + 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc :=
  gtp_thickPoint_of_adj_vert Vc hE hUp hnon


theorem rtc_eastThroat_discharge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
    (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
    (hSE : (![e, y - 1] : Site 2) ∈ Vc.support ∨
            (![e, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
    kns_ThickPoint Vc ∨
      ((![e, y - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![e, y - 1] : Site 2) ∉ Vc.support ∧
        s((![e, y] : Site 2), (![e + 1, y] : Site 2)) ∈ Vc.edges ∧
        s((![e, y] : Site 2), (![e, y + 1] : Site 2)) ∈ Vc.edges) := by
  by_cases hDnSup : (![e, y - 1] : Site 2) ∈ Vc.support
  · 
    exact Or.inl (rtc_thickPoint_of_eastThroat Vc hcyc hE hSeed hUp hDnSup)
  · 
    have hDnExt : (![e, y - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
      rcases hSE with h | h
      · exact absurd h hDnSup
      · exact h
    by_cases hseedEdge : s((![e, y] : Site 2), (![e + 1, y] : Site 2)) ∈ Vc.edges
    · by_cases hupEdge : s((![e, y] : Site 2), (![e, y + 1] : Site 2)) ∈ Vc.edges
      · exact Or.inr ⟨hDnExt, hDnSup, hseedEdge, hupEdge⟩
      · exact Or.inl (rtc_thickPoint_of_upWall_nonConsec Vc hE hUp hupEdge)
    · exact Or.inl (rtc_thickPoint_of_seedWall_nonConsec Vc hE hSeed hseedEdge)


end Lattice
end StatMech
