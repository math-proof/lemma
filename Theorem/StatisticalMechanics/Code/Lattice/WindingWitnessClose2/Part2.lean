/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.AnchoredCycleClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.WindingWitnessClose2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem wwc2_oddOrigin_of_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : wwc2_OriginInside ω hfin) :
    ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) :=
  wwc2_odd_of_mem_leftRegion _ h


theorem wwc2_exitDartWinds_of_turning_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, wwc2_oddOrigin_of_originInside (ω := ω) hfin hinside⟩
  have hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) :=
    acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)


theorem wwc2_exitDartWinds_of_cycle_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, wwc2_oddOrigin_of_originInside (ω := ω) hfin hinside⟩
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)


theorem wwc2_anchoredCycleExists_of_turning_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_exitDartWinds (ω := ω) hfin
    (wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin hturn hnp hinside)


theorem wwc2_pc_lt_one_of_turning_originInside
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧
          OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧
          wwc2_OriginInside ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  acc_pc_lt_one_of_exitDartWinds (fun ω hfin =>
    wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin (h ω hfin).1 (h ω hfin).2.1
      (h ω hfin).2.2)


theorem wwc2_unitCell_originInside :
    origin 2 ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
  rw [jec_mem_leftRegion]
  have horig : (origin 2) = (![0, 0] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [horig, mpl_unitCell_rayCount_eq_one]
  decide


theorem wwc2_unitCell_oddOrigin :
    ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) :=
  wwc2_odd_of_mem_leftRegion (mpl_orbitLoop unitCell ucBase) wwc2_unitCell_originInside


theorem wwc2_unitCell_primalLoop_isCycle : (mpl_orbitLoop unitCell ucBase).IsCycle :=
  mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    acc_unitCell_faceInj


theorem wwc2_unitCell_enclosesCell :
    (jec_leftRegion (mpl_orbitLoop unitCell ucBase)).Nonempty :=
  wwc2_leftRegion_nonempty (mpl_orbitLoop unitCell ucBase) wwc2_unitCell_primalLoop_isCycle


theorem wwc2_exitLoop_isCycle_of_turning (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
    (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle := by
  have hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) :=
    acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn
  exact mpl_orbitLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)


theorem wwc2_turning_enclosesCell (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
    ∃ z₀ : Site 2,
      z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :=
  wwc2_cycle_enclosesCell _ (wwc2_exitLoop_isCycle_of_turning (ω := ω) hfin hturn hnp)


theorem wwc2_originInside_of_reaches_enclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hreach : ∀ z₀ : Site 2,
      z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) →
      ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
        (∀ w ∈ p.support,
          w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    wwc2_OriginInside ω hfin := by
  obtain ⟨z₀, hz₀⟩ := wwc2_turning_enclosesCell (ω := ω) hfin hturn hnp
  obtain ⟨p, hp⟩ := hreach z₀ hz₀
  
  have hodd0 : ¬ Even (jec_rayCount z₀
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) :=
    (wwc2_odd_iff_mem_leftRegion _ z₀).mpr hz₀
  
  have hoddO : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) :=
    ooi_odd_of_connected_to_odd _ p hp hodd0
  exact (wwc2_odd_iff_mem_leftRegion _ (origin 2)).mp hoddO


theorem wwc2_exitDartWinds_of_turning_reaches (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hreach : ∀ z₀ : Site 2,
      z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) →
      ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
        (∀ w ∈ p.support,
          w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    acc_ExitDartWinds ω hfin :=
  wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin hturn hnp
    (wwc2_originInside_of_reaches_enclosed (ω := ω) hfin hturn hnp hreach)


end Lattice
end StatMech
