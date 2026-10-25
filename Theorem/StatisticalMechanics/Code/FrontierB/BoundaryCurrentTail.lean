/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.LocalCurrentTail.Part2
import Def.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
@[simp] theorem extendInteriorPlus_inside (interior : Finset V)
    (s : ConfigSpace ↑interior) (v : ↑interior) :
    extendInteriorPlus interior s v.1 = s v := by
  simp [extendInteriorPlus, v.2]

omit [Fintype V] in
@[simp] theorem extendInteriorPlus_outside (interior : Finset V)
    (s : ConfigSpace ↑interior) (v : V) (hv : v ∉ interior) :
    extendInteriorPlus interior s v = true := by
  simp [extendInteriorPlus, hv]

theorem prod_spin_extendInteriorPlus (interior : Finset V)
    (s : ConfigSpace ↑interior) (a : V → ℕ) :
    (∏ v : V, spin (extendInteriorPlus interior s) v ^ a v) =
      ∏ v : ↑interior, spin s v ^ a v.1 := by
  classical
  calc
    (∏ v : V, spin (extendInteriorPlus interior s) v ^ a v) =
        ∏ v ∈ interior, spin (extendInteriorPlus interior s) v ^ a v := by
      symm
      apply Finset.prod_subset (Finset.subset_univ interior)
      intro v hvuniv hvnot
      simp [extendInteriorPlus, hvnot]
    _ = ∏ v : ↑interior,
        spin (extendInteriorPlus interior s) v.1 ^ a v.1 := by
      exact Finset.prod_subtype interior (fun _ => Iff.rfl) _
    _ = ∏ v : ↑interior, spin s v ^ a v.1 := by
      apply Finset.prod_congr rfl
      intro v hv
      simp [spin, extendInteriorPlus, v.2]

theorem interiorSpinSum_monomial_eq (interior : Finset V)
    (n : Sharpness.Current V) :
    (∑ s : ConfigSpace ↑interior,
      ∏ e ∈ G.edgeFinset, bond (extendInteriorPlus interior s) e ^ n e) =
      if (sources G n) ∩ interior = ∅ then
        (2 : ℝ) ^ interior.card else 0 := by
  classical
  have hrewrite : ∀ s : ConfigSpace ↑interior,
      (∏ e ∈ G.edgeFinset, bond (extendInteriorPlus interior s) e ^ n e) =
        ∏ v : ↑interior, spin s v ^ incidentFlux G n v.1 := by
    intro s
    rw [prod_bond_pow_eq_prod_spin_pow]
    exact prod_spin_extendInteriorPlus interior s (incidentFlux G n)
  simp_rw [hrewrite]
  simp_rw [spin_eq_spinB]
  rw [← Fintype.prod_sum
    (fun v : ↑interior => fun b : Bool =>
      spinB b ^ incidentFlux G n v.1)]
  simp_rw [sum_spinB_pow]
  by_cases hsrc : (sources G n) ∩ interior = ∅
  · rw [if_pos hsrc]
    have heven : ∀ v : ↑interior, Even (incidentFlux G n v.1) := by
      intro v
      rw [← Nat.not_odd_iff_even]
      intro hodd
      have hvsrc : v.1 ∈ sources G n := by
        exact (Sharpness.mem_sources G).2 hodd
      have : v.1 ∈ (sources G n) ∩ interior := Finset.mem_inter.2 ⟨hvsrc, v.2⟩
      rw [hsrc] at this
      simp at this
    have hall :
        (∏ v : ↑interior,
          if Even (incidentFlux G n v.1) then (2 : ℝ) else 0) =
          ∏ _v : ↑interior, (2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [if_pos (heven v)]
    rw [hall]
    simp
  · rw [if_neg hsrc]
    have hne : ∃ v : V, v ∈ sources G n ∧ v ∈ interior := by
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hsrc
      exact ⟨v, (Finset.mem_inter.1 hv).1, (Finset.mem_inter.1 hv).2⟩
    obtain ⟨v, hvsrc, hvint⟩ := hne
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨v, hvint⟩ : ↑interior))
    have hvodd : Odd (incidentFlux G n v) := (Sharpness.mem_sources G).1 hvsrc
    rw [if_neg]
    exact Nat.not_even_iff_odd.mpr hvodd

end StatMech.FrontierB
