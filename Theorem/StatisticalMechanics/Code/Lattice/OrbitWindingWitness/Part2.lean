/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Def.StatisticalMechanics.Code.Lattice.OrbitWindingWitness
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem pww_oddRay_of_bdEdge_match (hfin : (cluster 2 ω (origin 2)).Finite) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2)) Vc)
    {q : Site 2} (hqK : q ∉ cluster 2 ω (origin 2))
    (hqfar : ∀ p ∈ Vc.support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk (origin 2) q) :
    ¬ Even (jec_rayCount (origin 2) Vc) := by
  
  have hoddK : ¬ Even (crossCount (cluster 2 ω (origin 2)) γ) :=
    orbit_origin_crossCount_odd (ω := ω) hfin hqK γ
  
  have heq : crossCount (jec_leftRegion Vc) γ = crossCount (cluster 2 ω (origin 2)) γ :=
    pww_crossCount_eq_of_bdEdge_match (jec_leftRegion Vc) (cluster 2 ω (origin 2))
      (fun e => (hmatch e).symm) γ
  have hoddL : ¬ Even (crossCount (jec_leftRegion Vc) γ) := by rw [heq]; exact hoddK
  
  exact (pww_oddRay_iff_oddCross_leftRegion Vc hqfar γ).mpr hoddL


theorem pww_origin_rayCount_odd (hfin : (cluster 2 ω (origin 2)).Finite) (e : Dart)
    (he : IsBoundaryDart (cluster 2 ω (origin 2)) e)
    (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2))
      (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
    {q : Site 2} (hqK : q ∉ cluster 2 ω (origin 2))
    (hqfar : ∀ p ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk (origin 2) q) :
    ¬ Even (jec_rayCount (origin 2)
      (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he)) :=
  pww_oddRay_of_bdEdge_match (ω := ω) hfin _ hmatch hqK hqfar γ


theorem pww_orbitIsLoop_of_bdEdge_match (hfin : (cluster 2 ω (origin 2)).Finite) (e : Dart)
    (he : IsBoundaryDart (cluster 2 ω (origin 2)) e)
    (ho : origin 2 ∈ cluster 2 ω (origin 2))
    (hExt : ∀ z, z ∉ cluster 2 ω (origin 2) → ∃ z0 : Site 2,
      ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support) ∧
      (∀ qq ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, z0 0 ≤ qq 0))
    (hInt : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∃ p : (hypercubicLattice 2).Walk z (origin 2),
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support))
    (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2))
      (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
    {q : Site 2} (hqK : q ∉ cluster 2 ω (origin 2))
    (hqfar : ∀ p ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk (origin 2) q) :
    ccs_OrbitIsLoop (cluster 2 ω (origin 2)) :=
  ooi_orbitIsLoop_of_witness (cluster 2 ω (origin 2)) hfin e he hExt ho
    (pww_origin_rayCount_odd (ω := ω) hfin e he hmatch hqK hqfar γ) hInt

end Lattice
end StatMech
