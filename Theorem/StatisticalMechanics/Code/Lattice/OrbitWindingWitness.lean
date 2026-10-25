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
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem pww_farLeft_notMem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2} (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0) :
    q ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  rw [jec_rayCount_eq_zero_of_right q Vc hq]
  exact Nat.even_iff.mpr rfl


theorem pww_oddRay_iff_oddCross_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2} (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk (origin 2) q) :
    (¬ Even (jec_rayCount (origin 2) Vc)) ↔
      (¬ Even (crossCount (jec_leftRegion Vc) γ)) := by
  have hqout : ¬ ¬ Even (jec_rayCount q Vc) :=
    not_not.mpr (by
      rw [jec_rayCount_eq_zero_of_right q Vc hq]; exact Nat.even_iff.mpr rfl)
  
  have hpar := crossCount_parity (jec_leftRegion Vc) γ
  simp only [jec_mem_leftRegion] at hpar
  
  constructor
  · intro hodd heven
    have hside := hpar.mp heven
    
    exact hqout (hside.mp hodd)
  · intro hcrossOdd hray
    apply hcrossOdd
    rw [hpar]
    
    constructor
    · intro h; exact absurd h (not_not.mpr hray)
    · intro h; exact absurd h hqout


theorem pww_crossCount_eq_of_bdEdge_match (S T : Set (Site 2))
    (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e)
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    crossCount S w = crossCount T w := by
  classical
  rw [crossCount, crossCount]
  refine List.countP_congr ?_
  intro e _he
  simp only [decide_eq_true_eq]
  exact hbd e


end Lattice
end StatMech
