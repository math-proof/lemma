/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem ahd_backbone_exists (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hall : aie_allConn ends m o x y) (hox : o ≠ x) (hxy : x ≠ y) :
    (∃ P ⊆ m, sources ends P = {o, x}) ∧ (∃ Q ⊆ m, sources ends Q = {x, y}) := by
  obtain ⟨hxy', _hoy', hox'⟩ := hall
  exact ⟨exists_conn_set ends m hox' hox, exists_conn_set ends m hxy' hxy⟩


theorem ahd_mass_reroute_xy_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {x, y}) = aie_mass ends m φ A := by
  obtain ⟨hxy', _, _⟩ := hall
  unfold aie_mass
  rw [asd_switching_weighted_indicator ends m hnd A hm hxy φ hφ, if_pos hxy', one_mul]


theorem ahd_mass_reroute_oy_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hoy : o ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {o, y}) = aie_mass ends m φ A := by
  obtain ⟨_, hoy', _⟩ := hall
  unfold aie_mass
  rw [asd_switching_weighted_indicator ends m hnd A hm hoy φ hφ, if_pos hoy', one_mul]


theorem ahd_mass_reroute_ox_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {o, x}) = aie_mass ends m φ A := by
  obtain ⟨_, _, hox'⟩ := hall
  unfold aie_mass
  rw [asd_switching_weighted_indicator ends m hnd A hm hox φ hφ, if_pos hox', one_mul]


theorem ahd_mass_reroute₂_eq (ends : ι → Sym2 V) (m : Finset ι) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ2 : ∀ K P Q, P ⊆ m → Q ⊆ m → K ⊆ m → φ ((K ∆ P) ∆ Q) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {o, x} ∆ {x, y}) = aie_mass ends m φ A := by
  obtain ⟨hxy', _, hox'⟩ := hall
  unfold aie_mass
  exact asd_signDominance₂_edgecopy ends m A hox hxy hox' hxy' φ hφ2


theorem ahd_gap_eq_neg_two_mass (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A := by
  unfold aie_gap
  rw [ahd_mass_reroute_xy_eq ends m hnd A hm hxy φ hφ hall,
      ahd_mass_reroute_oy_eq ends m hnd A hm hoy φ hφ hall,
      ahd_mass_reroute_ox_eq ends m hnd A hm hox φ hφ hall]
  ring


theorem ahd_per_super_allConn_gap_nonneg_iff (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    0 ≤ aie_gap ends m φ A o x y ↔ aie_mass ends m φ A = 0 := by
  rw [ahd_gap_eq_neg_two_mass ends m hnd A hm hox hoy hxy φ hφ hall]
  have hnn := aie_mass_nonneg ends m φ hφnn A
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num


theorem ahd_closure_iff_hdom (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    (0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y)
      ↔ (2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
          ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) := by
  rw [aie_inclusion_exclusion_decomp ends M hnd A hm hox hoy hxy Φ hΦ]
  constructor <;> intro h <;> linarith


end RandomCurrent
end Sharpness
end StatMech
