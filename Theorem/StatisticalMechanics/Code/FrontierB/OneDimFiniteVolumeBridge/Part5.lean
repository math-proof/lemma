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
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part5
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma chainSiteFinset_eq_boxFinset (n : ℕ) :
    chainSiteFinset n = boxFinset 1 n := by
  ext x
  rw [chainSiteFinset, Finset.mem_image, mem_boxFinset]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Finset.mem_Icc] at hz
    exact (site1_mem_box_iff z n).mpr hz
  · intro hx
    refine ⟨site1Coord x, ?_, site1_site1Coord x⟩
    rw [Finset.mem_Icc]
    apply (site1_mem_box_iff (site1Coord x) n).mp
    simpa only [site1_site1Coord] using hx

lemma sum_bondFinsetTouch_eq_chain (n : ℕ) (sigma : ConfigSpace (Site 1)) :
    (∑ e ∈ bondFinsetTouch 1 n, bond sigma e) =
      ∑ z ∈ Finset.Icc (-(n : ℤ) - 1) (n : ℤ),
        spin sigma (site1 z) * spin sigma (site1 (z + 1)) := by
  rw [← chainBondFinset_eq_bondFinsetTouch, chainBondFinset]
  rw [Finset.sum_image (Set.injOn_of_injective chainBond_injective)]
  apply Finset.sum_congr rfl
  intro z _
  simp [chainBond, bond_mk]

lemma sum_boxFinset_eq_chain (n : ℕ) (sigma : ConfigSpace (Site 1)) :
    (∑ x ∈ boxFinset 1 n, spin sigma x) =
      ∑ z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), spin sigma (site1 z) := by
  rw [← chainSiteFinset_eq_boxFinset, chainSiteFinset]
  rw [Finset.sum_image (Set.injOn_of_injective site1_injective)]


lemma sum_range_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (L : ℤ) (m : ℕ) (f : ℤ → M) :
    (∑ k ∈ Finset.range (m + 1), f (L + k)) =
      ∑ z ∈ Finset.Icc L (L + m), f z := by
  refine Finset.sum_bij
    (fun (k : ℕ) (_ : k ∈ Finset.range (m + 1)) => L + (k : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc]
    simp only [Finset.mem_range] at hk
    dsimp
    omega
  · intro k hk l hl heq
    dsimp at heq
    omega
  · intro z hz
    rw [Finset.mem_Icc] at hz
    let k := (z - L).toNat
    have hk : k < m + 1 := by
      dsimp [k]
      omega
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    dsimp [k]
    omega
  · intro k hk
    rfl

lemma sum_adjacent_half (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (f k + f (k + 1)) / 2) =
      (f 0 + f (m + 1)) / 2 + ∑ k ∈ Finset.range m, f (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ]
      ring


end StatMech.FrontierB
