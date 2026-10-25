/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.AnchoredCycleClose.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem acc_anchoredCycleExists_of_exitDartWinds (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : acc_ExitDartWinds ω hfin) : AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_oddOrigin (ω := ω) hfin h.1 h.2


theorem acc_pcAnchoredEnclosure_of_exitDartWinds
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        acc_ExitDartWinds ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  refine pcAnchoredEnclosure_of_cycleHasLeftFace (fun ω hfin => ?_)
  exact acc_cycleHasLeftFace_of_oddOrigin (ω := ω) hfin (h ω hfin).1 (h ω hfin).2


theorem acc_pc_lt_one_of_exitDartWinds
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        acc_ExitDartWinds ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_lt_one_of_enclosure (acc_pcAnchoredEnclosure_of_exitDartWinds h)


theorem acc_origin_mem_cluster (_hfin : (cluster 2 ω (origin 2)).Finite) :
    (origin 2) ∈ cluster 2 ω (origin 2) :=
  self_mem_cluster ω (origin 2)


theorem acc_oddOrigin_of_cycle_interior_intConn (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) := by
  
  have hcyc : (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle :=
    mpl_orbitLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
      (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)
  
  obtain ⟨z0, hz0odd⟩ :=
    eaw_cycle_oddCell' (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) hcyc
  
  have hz0K : z0 ∈ cluster 2 ω (origin 2) := hint z0 hz0odd
  
  obtain ⟨p, hp_supp⟩ :=
    hIntConn (origin 2) (acc_origin_mem_cluster (ω := ω) hfin) z0 hz0K hz0odd
  
  exact (ooi_odd_of_connected_to_odd
    (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) p hp_supp hz0odd)


theorem acc_exitDartWinds_of_cycle_interior (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, acc_oddOrigin_of_cycle_interior_intConn (ω := ω) hfin hp hnp hint hIntConn⟩
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)


theorem acc_period_ge_three_of_fullRevolution (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
    3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) := by
  have := orbitPeriod_ge_four_of_fullRevolution (cluster 2 ω (origin 2))
    (acc_exitSub (ω := ω) hfin) hturn
  omega


theorem acc_exitDartWinds_of_turning_interior (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    acc_ExitDartWinds ω hfin :=
  acc_exitDartWinds_of_cycle_interior (ω := ω) hfin
    (acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn) hnp hint hIntConn


theorem acc_unitCell_faceInj :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1))
      (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
  rw [unitCell_orbitPeriod_eq_four, show ucBase.1 = ucDart0 from rfl]
  exact unitCell_orbitFace_injOn


theorem acc_unitCell_faceLoop_isCycle : (mpl_orbitFaceLoop unitCell ucBase).IsCycle :=
  mpl_orbitFaceLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    acc_unitCell_faceInj


theorem acc_unitCell_winds :
    (mpl_orbitFaceLoop unitCell ucBase).IsCycle ∧
      ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) := by
  refine ⟨acc_unitCell_faceLoop_isCycle, ?_⟩
  have horig : (origin 2) = (![0, 0] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [horig, mpl_unitCell_rayCount_eq_one]
  decide


theorem acc_unitCell_hasLeftSupportFace :
    ∃ f ∈ (mpl_orbitLoop unitCell ucBase).support, f 0 ≤ -1 := by
  have hodd := acc_unitCell_winds.2
  have hpos : 0 < jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase) := by
    rcases Nat.eq_zero_or_pos (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) with h | h
    · exact absurd (by rw [h]; exact Nat.even_iff.mpr rfl) hodd
    · exact h
  obtain ⟨f, hf, hcol⟩ := acc_oddRay_mem_support (mpl_orbitLoop unitCell ucBase) hpos
  have horig0 : (origin 2) 0 = 0 := rfl
  exact ⟨f, hf, by rw [horig0] at hcol; omega⟩


end Lattice
end StatMech
