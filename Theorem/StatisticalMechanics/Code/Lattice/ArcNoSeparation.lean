/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Def.StatisticalMechanics.Code.Lattice.ArcNoSeparation
open Set SimpleGraph


namespace StatMech

namespace Lattice

theorem arcns_walk_of_connected {B : Set (Site 2)} (h : arcns_OffSupportConnected B)
    {x y : Site 2} (hx : x ∉ B) (hy : y ∉ B) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B :=
  (ffc_reachable_iff_offSupportWalk hx).mp (h x y hx hy)


theorem arcns_farLeft_connected (B : Set (Site 2)) (b : ℤ) (hb : ∀ q ∈ B, b ≤ q 0)
    (z1 z2 : Site 2) (h1 : z1 0 ≤ b - 1) (h2 : z2 0 ≤ b - 1) :
    ∃ p : (hypercubicLattice 2).Walk z1 z2, ∀ w ∈ p.support, w ∉ B := by
  have e1 : (![z1 0, z1 1] : Site 2) = z1 := by funext i; fin_cases i <;> rfl
  have e2 : (![z2 0, z2 1] : Site 2) = z2 := by funext i; fin_cases i <;> rfl
  refine ⟨(sw_lshape (z1 0) (z1 1) (z2 0) (z2 1)).copy e1 e2, ?_⟩
  intro w hw hwB
  rw [Walk.support_copy, sw_lshape_support_eq] at hw
  have hbw : b ≤ w 0 := hb w hwB
  rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · simp only [Matrix.cons_val_zero] at hbw
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨_, hle⟩ | ⟨_, hle⟩ <;> omega
  · simp only [Matrix.cons_val_zero] at hbw
    omega


end Lattice
end StatMech
