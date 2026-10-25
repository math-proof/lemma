/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part2
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma site1_mem_box_iff (z : ℤ) (n : ℕ) :
    site1 z ∈ box 1 n ↔ -(n : ℤ) ≤ z ∧ z ≤ (n : ℤ) := by
  rw [mem_box]
  simp only [site1, Fin.forall_fin_one]
  constructor
  · intro hz
    have hz' : (z.natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hz
    rw [← Int.abs_eq_natAbs, abs_le] at hz'
    exact hz'
  · intro hz
    have hz' : |z| ≤ (n : ℤ) := abs_le.mpr hz
    rw [Int.abs_eq_natAbs] at hz'
    exact_mod_cast hz'

lemma site1_adj_iff (z w : ℤ) :
    (hypercubicLattice 1).Adj (site1 z) (site1 w) ↔ (z - w).natAbs = 1 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_one]
  rfl

lemma mem_bondFinsetTouch_mk_iff (n : ℕ) (x y : Site 1) :
    s(x, y) ∈ bondFinsetTouch 1 n ↔
      (hypercubicLattice 1).Adj x y ∧ (x ∈ box 1 n ∨ y ∈ box 1 n) := by
  constructor
  · intro he
    unfold bondFinsetTouch at he
    rw [Finset.mem_image] at he
    obtain ⟨p, hp, hpe⟩ := he
    unfold bondPairsTouch at hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hadj, htouch⟩ := hp
    rw [Sym2.eq_iff] at hpe
    rcases hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hadj, htouch⟩
    · exact ⟨hadj.symm, htouch.symm⟩
  · rintro ⟨hadj, htouch⟩
    exact StatMech.Lattice.mk_mem_bondFinsetTouch hadj htouch


end StatMech.FrontierB
