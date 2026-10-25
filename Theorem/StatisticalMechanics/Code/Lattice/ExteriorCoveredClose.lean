/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorCoveredClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OutsideReachesClose.Part2
import Def.StatisticalMechanics.Code.Lattice.ExteriorCoveredClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem ecc_reach_offSupport (Vc : (hypercubicLattice 2).Walk a a) {z w : Site 2}
    (hzoff : z ∉ Vc.support) (h : (offSupport Vc).Reachable z w) : w ∉ Vc.support := by
  obtain ⟨pw, hpw⟩ := offSupport_reachable_to_offSupportWalk Vc h hzoff
  exact hpw w pw.end_mem_support


theorem ecc_reaches_right_band (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hstep : ecc_RightStep Vc R)
    (z : Site 2) (hzout : z ∉ jec_leftRegion Vc) (hzoff : z ∉ Vc.support) :
    ∃ w : Site 2, (R : ℤ) + 1 ≤ w 0 ∧ (offSupport Vc).Reachable z w := by
  generalize hm : ((R : ℤ) + 1 - z 0).toNat = m
  induction m using Nat.strong_induction_on generalizing z with
  | _ m ih =>
    rcases le_or_gt ((R : ℤ) + 1) (z 0) with hge | hlt
    · exact ⟨z, hge, SimpleGraph.Reachable.refl _⟩
    · have hzR : z 0 ≤ (R : ℤ) := by omega
      obtain ⟨w, hprog, hreach⟩ := hstep z hzout hzoff hzR
      have hwoff : w ∉ Vc.support := ecc_reach_offSupport Vc hzoff hreach
      have hwout : w ∉ jec_leftRegion Vc :=
        offSupport_component_monochromatic_out Vc hzout hreach hzoff
      have hmw : ((R : ℤ) + 1 - w 0).toNat < m := by rw [← hm]; omega
      obtain ⟨u, hu, hwu⟩ := ih _ hmw w hwout hwoff rfl
      exact ⟨u, hu, hreach.trans hwu⟩


theorem ecc_outsideReachesExterior_of_rightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
    (hstep : ecc_RightStep Vc R) :
    oc_OutsideReachesExterior Vc R := by
  intro z hz
  have hzoff : z ∉ Vc.support := hoffOut z hz
  obtain ⟨w, hw, hreach⟩ := ecc_reaches_right_band Vc R hstep z hz hzoff
  have hwExt : w ∈ exterior 2 R := oc_mem_exterior_of_col_high R hw
  exact ⟨w, hwExt, orc_offSupportLattice_reachable_of_offSupport Vc hzoff hreach⟩


theorem ecc_exteriorCovered_of_rightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
    {beacon : Site 2} (hbExt : beacon ∈ exterior 2 R)
    (hstep : ecc_RightStep Vc R) :
    orc_ExteriorCovered Vc beacon :=
  orc_exteriorCovered_of_outsideReachesExterior Vc R hsupp hbExt
    (ecc_outsideReachesExterior_of_rightStep Vc R hoffOut hstep)


theorem ecc_two_components_of_rightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hoffOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → s ∉ Vc.support)
    (hstep : ecc_RightStep Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  oc_two_components_of_outsideReaches Vc R hsupp hp hq hInOff
    (ecc_outsideReachesExterior_of_rightStep Vc R hoffOut hstep)


theorem ecc_rightNeighbor_step (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hzoff : z ∉ Vc.support) (hnbOff : (![z 0 + 1, z 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0 + 1, z 1] := by
  have hadj : (hypercubicLattice 2).Adj z ![z 0 + 1, z 1] := by
    have h := sw_adj_horizSucc (z 1) (z 0)
    have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
    rw [hzeq]; exact h
  exact (Adj.reachable ⟨hadj, hzoff, hnbOff⟩ : (offSupport Vc).Reachable _ _)


end Lattice
end StatMech
