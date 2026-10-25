/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Def.StatisticalMechanics.Code.Walls.wisindicatorsteps
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wis_ind_in_01 (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (c : ℤ) :
    wis_ind z Vc c = 0 ∨ wis_ind z Vc c = 1 := by
  unfold wis_ind
  have h := Int.emod_two_eq_zero_or_one (jec_rayCount (![c, z 1] : Site 2) Vc : ℤ)
  tauto


theorem wis_rowCell_step (z : Site 2) (c : ℤ) :
    (![c + 1, z 1] : Site 2) 0 = (![c, z 1] : Site 2) 0 + 1 ∧
      (![c + 1, z 1] : Site 2) 1 = (![c, z 1] : Site 2) 1 := by
  constructor <;> simp


theorem wis_ind_step_neq_iff (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c : ℤ) :
    wis_ind z Vc (c + 1) ≠ wis_ind z Vc c ↔
      Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) := by
  have hstep := wis_rowCell_step z c
  have hflip := rpc_horizontalFlip_iff Vc (![c, z 1] : Site 2) (![c + 1, z 1] : Site 2)
    hstep.1 hstep.2
  
  rw [← hflip]
  unfold wis_ind
  set pc := jec_rayCount (![c, z 1] : Site 2) Vc with hpc
  set pc1 := jec_rayCount (![c + 1, z 1] : Site 2) Vc with hpc1
  
  have hpar : ∀ n : ℕ, (Even n ↔ (n : ℤ) % 2 = 0) := by
    intro n
    rw [← Int.even_coe_nat, Int.even_iff]
  constructor
  · intro hne
    have h0 := hpar pc
    have h1 := hpar pc1
    have hpc01 := Int.emod_two_eq_zero_or_one (pc : ℤ)
    have hpc101 := Int.emod_two_eq_zero_or_one (pc1 : ℤ)
    by_cases hep : Even pc <;> by_cases hep1 : Even pc1 <;>
      first | (simp_all; done) | (simp_all; omega)
  · intro hiff
    have h0 := hpar pc
    have h1 := hpar pc1
    have hpc01 := Int.emod_two_eq_zero_or_one (pc : ℤ)
    have hpc101 := Int.emod_two_eq_zero_or_one (pc1 : ℤ)
    by_cases hep : Even pc <;> by_cases hep1 : Even pc1 <;>
      first | (simp_all; done) | (simp_all; omega)


end Lattice
end StatMech
