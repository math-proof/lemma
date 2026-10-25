/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Def.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem mem_boxCluster (m n : ℕ) (x : Site 2) :
    x ∈ boxCluster m n ↔ 0 ≤ x 0 ∧ x 0 ≤ m ∧ 0 ≤ x 1 ∧ x 1 ≤ n := by
  unfold boxCluster; rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hab
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨(x 0, x 1), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]; omega
    · funext i; fin_cases i <;> rfl


theorem mem_box_coords (m n : ℕ) (p q : ℤ) :
    (![p, q] : Site 2) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      0 ≤ p ∧ p ≤ m ∧ 0 ≤ q ∧ q ≤ n := by
  rw [Finset.mem_coe, mem_boxCluster]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]


theorem origin_mem_boxCluster (m n : ℕ) : origin 2 ∈ boxCluster m n := by
  rw [mem_boxCluster, origin_eq_zerozero]; simp


theorem boxR_step (m n : ℕ) (a b : ℤ) (h1 : 0 ≤ a) (h2 : a + 1 ≤ m) (h3 : 0 ≤ b) (h4 : b ≤ n) :
    (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![a, b] ![a + 1, b] := by
  refine ⟨latAdj_right a b, ?_, ?_⟩ <;>
    · rw [Finset.mem_coe, mem_boxCluster]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega


theorem boxT_step (m n : ℕ) (a b : ℤ) (h1 : 0 ≤ a) (h2 : a ≤ m) (h3 : 0 ≤ b) (h4 : b + 1 ≤ n) :
    (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![a, b] ![a, b + 1] := by
  refine ⟨latAdj_top a b, ?_, ?_⟩ <;>
    · rw [Finset.mem_coe, mem_boxCluster]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega


theorem reach_xaxis (m n : ℕ) (k : ℕ) (hk : k ≤ m) :
    (latticeOn (↑(boxCluster m n) : Set (Site 2))).Reachable ![(0:ℤ), 0] ![(k:ℤ), 0] := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ j ih =>
    have hj : j ≤ m := by omega
    have step : (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![(j:ℤ), 0] ![(j:ℤ) + 1, 0] :=
      boxR_step m n (j:ℤ) 0 (by positivity)
        (by exact_mod_cast (by omega : (j:ℤ) + 1 ≤ m)) (le_refl 0) (by positivity)
    rw [show ((j:ℤ) + 1) = ((j + 1 : ℕ) : ℤ) from by push_cast; ring] at step
    exact (ih hj).trans (SimpleGraph.Adj.reachable step)


theorem reach_ycol (m n : ℕ) (a : ℤ) (ha0 : 0 ≤ a) (ham : a ≤ m) (k : ℕ) (hk : k ≤ n) :
    (latticeOn (↑(boxCluster m n) : Set (Site 2))).Reachable ![a, 0] ![a, (k:ℤ)] := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ j ih =>
    have hj : j ≤ n := by omega
    have step : (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![a, (j:ℤ)] ![a, (j:ℤ) + 1] :=
      boxT_step m n a (j:ℤ) ha0 ham (by positivity)
        (by exact_mod_cast (by omega : (j:ℤ) + 1 ≤ n))
    rw [show ((j:ℤ) + 1) = ((j + 1 : ℕ) : ℤ) from by push_cast; ring] at step
    exact (ih hj).trans (SimpleGraph.Adj.reachable step)


theorem boxCluster_isConnectedCluster (m n : ℕ) : IsConnectedCluster (boxCluster m n) := by
  refine ⟨origin_mem_boxCluster m n, ?_⟩
  intro x hx
  rw [mem_boxCluster] at hx
  obtain ⟨h0, h1, h2, h3⟩ := hx
  rw [origin_eq_zerozero, show x = ![x 0, x 1] from by funext i; fin_cases i <;> rfl]
  set kx := (x 0).toNat with hkx
  set ky := (x 1).toNat with hky
  have hx0 : (x 0) = (kx : ℤ) := by rw [hkx]; omega
  have hx1 : (x 1) = (ky : ℤ) := by rw [hky]; omega
  have hkxm : kx ≤ m := by rw [hkx]; omega
  have hkyn : ky ≤ n := by rw [hky]; omega
  rw [hx0, hx1]
  exact (reach_xaxis m n kx hkxm).trans
    (reach_ycol m n (kx:ℤ) (by positivity) (by exact_mod_cast hkxm) ky hkyn)


end Lattice
end StatMech
