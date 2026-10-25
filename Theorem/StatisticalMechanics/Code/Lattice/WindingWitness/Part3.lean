/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Def.StatisticalMechanics.Code.Lattice.WindingWitness.Part2
open SimpleGraph Function Set Finset


namespace StatMech

namespace Lattice

theorem wwit_winding_witness_of_tailOdd (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hprim : wwit_TailOdd K hK a) :
    ∃ z₀ : Site 2, z₀ ∈ K ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2)) := by
  obtain ⟨i, hodd⟩ := hprim
  exact ⟨((dartNext K)^[i] a.1).tail, wwit_orbit_tail_mem K a i, hodd⟩


theorem wwit_starHull_winding_witness (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hprim : wwit_TailOdd (ndt_StarHull K) hSK a) :
    ∃ z₀ : Site 2, z₀ ∈ ndt_StarHull K ∧
      ¬ Even (jec_rayCount z₀ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2)) :=
  wwit_winding_witness_of_tailOdd (ndt_StarHull K) hSK a hprim


theorem wwit_starHull_bdEdgeMatch_of_tailOdd (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (i : ℕ)
    (hodd : ¬ Even (jec_rayCount ((dartNext (ndt_StarHull K))^[i] a.1).tail
      (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2)))
    (hExt : ∀ z, z ∉ ndt_StarHull K → ∃ z0 : Site 2,
      ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support) ∧
      (∀ q ∈ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support, z0 0 ≤ q 0))
    (hInt : ∀ z, z ∈ ndt_StarHull K →
      ∃ p : (hypercubicLattice 2).Walk z ((dartNext (ndt_StarHull K))^[i] a.1).tail,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support)) :
    pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2) :=
  pbs_bdEdgeMatch_starHull_of_winding K hSK a.1 a.2 hExt
    (wwit_orbit_tail_mem (ndt_StarHull K) a i) hodd hInt


end Lattice
end StatMech
