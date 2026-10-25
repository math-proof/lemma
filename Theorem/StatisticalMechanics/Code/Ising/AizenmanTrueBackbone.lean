/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean -/

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
import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2
import Def.StatisticalMechanics.Code.Ising.AizenmanTrueBackbone
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent


local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

local notation "compK" => StatMech.Sharpness.RandomCurrent.compOf

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem atb_conn_iff_mem_backbone (ends : ι → Sym2 V) (m : Finset ι) (o z : V) :
    connK ends m o z ↔ z ∈ atb_backbone ends m o := by
  unfold atb_backbone StatMech.Sharpness.RandomCurrent.compOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]


theorem atb_conn_xy_of_mem_backbone (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hx : x ∈ atb_backbone ends m o) (hy : y ∈ atb_backbone ends m o) :
    connK ends m x y := by
  rw [← atb_conn_iff_mem_backbone] at hx hy
  exact Relation.ReflTransGen.trans (connK_symm ends m hx) hy


theorem atb_allConn_of_xy_in_backbone (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hx : x ∈ atb_backbone ends m o) (hy : y ∈ atb_backbone ends m o) :
    aie_allConn ends m o x y := by
  have hox : connK ends m o x := (atb_conn_iff_mem_backbone ends m o x).2 hx
  have hoy : connK ends m o y := (atb_conn_iff_mem_backbone ends m o y).2 hy
  exact ⟨atb_conn_xy_of_mem_backbone ends m hx hy, hoy, hox⟩


theorem atb_allConn_iff_xy_in_backbone (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    aie_allConn ends m o x y
      ↔ (x ∈ atb_backbone ends m o ∧ y ∈ atb_backbone ends m o) := by
  constructor
  · rintro ⟨_, hoy, hox⟩
    exact ⟨(atb_conn_iff_mem_backbone ends m o x).1 hox,
           (atb_conn_iff_mem_backbone ends m o y).1 hoy⟩
  · rintro ⟨hx, hy⟩
    exact atb_allConn_of_xy_in_backbone ends m hx hy


theorem atb_signDominance_per_backbone (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {u v : V} (huv : u ≠ v) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    aie_mass ends m φ (A ∆ {u, v}) ≤ aie_mass ends m φ A := by
  unfold aie_mass
  exact asd_signDominance ends m hnd A hm huv φ hφnn (fun K P hP hK => hφ K P hP hK)


theorem atb_conditioned_gap_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    aie_gap ends m φ A o x y = aie_mass ends m φ A * asd_ghsBackboneFactor ends m o x y :=
  aie_gap_eq ends m hnd A hm hox hoy hxy φ hφ


theorem atb_conditioned_gap_allBackbone (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hx : x ∈ atb_backbone ends m o) (hy : y ∈ atb_backbone ends m o) :
    aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A :=
  aie_gap_allConn ends m hnd A hm hox hoy hxy φ hφ
    (atb_allConn_of_xy_in_backbone ends m hx hy)


theorem atb_conditioned_decomp (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    ∑ m ∈ M, aie_gap ends m (Φ m) A o x y
      = (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
        - 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) :=
  aie_inclusion_exclusion_decomp ends M hnd A hm hox hoy hxy Φ hΦ


end Ising
end StatMech
