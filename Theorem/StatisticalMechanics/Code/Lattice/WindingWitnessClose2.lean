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
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem wwc2_odd_iff_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) :
    ¬ Even (jec_rayCount z Vc) ↔ z ∈ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion]


theorem wwc2_odd_of_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∈ jec_leftRegion Vc) :
    ¬ Even (jec_rayCount z Vc) :=
  (wwc2_odd_iff_mem_leftRegion Vc z).mpr hz


theorem wwc2_far_not_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2} (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1) :
    q ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion]; push Not
  exact jec_ray_even_far Vc q hq


theorem wwc2_even_of_connected_to_far {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z q : Site 2} (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (p : (hypercubicLattice 2).Walk z q) (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    Even (jec_rayCount z Vc) := by
  have hsame := jlri_sameRegion_along_offSupport_walk Vc p hp
  by_contra hodd
  have hzmem : z ∈ jec_leftRegion Vc := by rw [jec_mem_leftRegion]; exact hodd
  exact wwc2_far_not_mem_leftRegion Vc hq (hsame.mp hzmem)


theorem wwc2_cycle_enclosesCell {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    ∃ z : Site 2, z ∈ jec_leftRegion Vc := by
  obtain ⟨z, hz⟩ := eaw_cycle_oddCell' Vc hcyc
  exact ⟨z, (wwc2_odd_iff_mem_leftRegion Vc z).mp hz⟩


theorem wwc2_leftRegion_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    (jec_leftRegion Vc).Nonempty :=
  wwc2_cycle_enclosesCell Vc hcyc


theorem wwc2_leftRegion_nonempty_finite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc).Nonempty ∧ (jec_leftRegion Vc).Finite :=
  ⟨wwc2_leftRegion_nonempty Vc hcyc, egf_leftRegion_finite Vc R hsupp⟩


end Lattice
end StatMech
