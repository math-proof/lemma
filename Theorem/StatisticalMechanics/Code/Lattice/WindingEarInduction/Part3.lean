/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFull
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Def.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem wei_windingWitness_of_descent (hres : wei_WindingSaturatingWitness)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : wei_WindingWitness K a := by
  generalize hn : K.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n IH =>
    subst hn
    rcases Nat.lt_or_ge K.ncard 2 with hlt | hge
    · 
      have h1 : K.ncard = 1 := by
        have hpos : 0 < K.ncard := (Set.ncard_pos hK).mpr hne
        omega
      obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1
      subst hv
      exact wei_singleton_windingWitness v a
    · 
      by_cases hsat : K ⊆ bpc_orbitFootprint K a
      · exact hres K hK hge a hsat
      · 
        rw [Set.not_subset] at hsat
        obtain ⟨c, hcK, hc⟩ := hsat
        have hne_tail : c ≠ a.1.tail := bpc_ne_tail_of_not_footprint K a c hc
        have hbd : IsBoundaryDart (K \ {c}) a.1 :=
          bpc_isBoundaryDart_diff_singleton K c a.1 a.2 hne_tail
        set a' : {e : Dart // IsBoundaryDart (K \ {c}) e} := ⟨a.1, hbd⟩ with ha'
        have hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1) :=
          bpc_notProbed_of_not_footprint K a c hc
        have hK' : (K \ {c}).Finite := hK.subset Set.diff_subset
        
        have hcard_eq : (K \ {c}).ncard = K.ncard - 1 := Set.ncard_diff_singleton_of_mem hcK
        have hne' : (K \ {c}).Nonempty := by
          rw [← Set.ncard_pos hK', hcard_eq]; omega
        have hncard_lt : (K \ {c}).ncard < K.ncard := by rw [hcard_eq]; omega
        have hw' : wei_WindingWitness (K \ {c}) a' :=
          IH (K \ {c}).ncard hncard_lt (K \ {c}) hK' hne' a' rfl
        exact wei_windingWitness_transfer_diff_singleton K c a a' (by rw [ha']) hnp hw'


theorem wei_starHull_windingWitness_of_residue (hres : wei_WindingSaturatingWitness)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    wei_WindingWitness (ndt_StarHull K) a :=
  wei_windingWitness_of_descent hres (ndt_StarHull K) hSK hne a


theorem wei_insideHalf_of_windingWitness (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {z0 : Site 2} (_hz0 : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
    ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  intro z hz
  obtain ⟨p, hp⟩ := hInt z hz
  exact ooi_odd_of_connected_to_odd (mpl_orbitLoop K a) p hp hodd0


theorem wei_starHull_bdEdgeMatch_of_residue (hres : wei_WindingSaturatingWitness)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hInt : ∀ z0, z0 ∈ ndt_StarHull K →
      ∀ z, z ∈ ndt_StarHull K → ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (ndt_StarHull K) a).support))
    (hout : ∀ z, z ∉ ndt_StarHull K →
      Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a))) :
    pww_BdEdgeMatch (ndt_StarHull K) (mpl_orbitLoop (ndt_StarHull K) a) := by
  obtain ⟨z0, hz0K, hz0odd⟩ := wei_starHull_windingWitness_of_residue hres K hSK hne a
  have hin : ∀ z, z ∈ ndt_StarHull K →
      ¬ Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a)) :=
    wei_insideHalf_of_windingWitness (ndt_StarHull K) a hz0K hz0odd (hInt z0 hz0K)
  exact jsf_starHull_bdEdgeMatch_of_rayParity K a hin hout


theorem wei_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  refine ⟨![0, 0], ?_, ?_⟩
  · simp only [unitCell, Set.mem_singleton_iff]
  · rw [mpl_unitCell_rayCount_eq_one]; decide


end Lattice
end StatMech
