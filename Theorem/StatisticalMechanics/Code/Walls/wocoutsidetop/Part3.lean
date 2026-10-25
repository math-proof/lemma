/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.Walls.wocoutsidetop.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem woc_component_has_lexMax (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hfin : (offSupportComponent Vc seed).Finite) :
    ∃ m ∈ offSupportComponent Vc seed,
      ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m := by
  have hne : (offSupportComponent Vc seed).Nonempty :=
    ⟨seed, seed_mem_offSupportComponent Vc seed⟩
  have hfne : hfin.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image hfin.toFinset woc_lexKey hfne
  refine ⟨m, by rwa [Set.Finite.mem_toFinset] at hm, ?_⟩
  intro v hv
  exact hmax v (by rwa [Set.Finite.mem_toFinset])


theorem woc_up_not_mem_of_lexMax (Vc : (hypercubicLattice 2).Walk a a) {seed m : Site 2}
    (hmax : ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m) :
    (![m 0, m 1 + 1] : Site 2) ∉ offSupportComponent Vc seed := by
  intro hup
  have h := hmax _ hup
  unfold woc_lexKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem woc_extreme_up_onSupport (Vc : (hypercubicLattice 2).Walk a a) {seed m : Site 2}
    (hsoff : seed ∉ Vc.support) (hm : m ∈ offSupportComponent Vc seed)
    (hmax : ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m) :
    (![m 0, m 1 + 1] : Site 2) ∈ Vc.support := by
  by_contra hupoff
  
  have hmoff : m ∉ Vc.support := offSupportComponent_offSupport Vc hsoff hm
  
  have hmeq : m = ![m 0, m 1] := by ext i; fin_cases i <;> simp
  
  have hadj : (hypercubicLattice 2).Adj m (![m 0, m 1 + 1]) := by
    rw [hmeq]; exact sw_adj_vertSucc (m 0) (m 1)
  
  have hadj' : (offSupport Vc).Adj m (![m 0, m 1 + 1]) := ⟨hadj, hmoff, hupoff⟩
  
  have hreach : (offSupport Vc).Reachable seed (![m 0, m 1 + 1]) :=
    ((mem_offSupportComponent Vc).mp hm).trans hadj'.reachable
  have hupmem : (![m 0, m 1 + 1] : Site 2) ∈ offSupportComponent Vc seed :=
    (mem_offSupportComponent Vc).mpr hreach
  exact woc_up_not_mem_of_lexMax Vc hmax hupmem


end Lattice
end StatMech
