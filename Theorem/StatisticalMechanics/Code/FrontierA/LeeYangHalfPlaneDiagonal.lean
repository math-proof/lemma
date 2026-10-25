/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
import Structure.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal
open Filter Metric Set Topology
open scoped UniformConvergence


namespace StatMech.FrontierA

open StatMech.FK


theorem holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
    (E : CompactExhaustion U) :
    IsLocallyUniformlySequentiallyPrecompact F U := by
  classical
  intro φ hφ
  let X : ℕ → Type := fun n => E.sets n →ᵤ ℂ
  let S : ∀ n, Set (X n) := fun n => closure (Set.range (fun k =>
    UniformFun.ofFun (fun z : E.sets n => F (φ k) z)))
  have hS : ∀ n, IsCompact (S n) := by
    intro n
    simpa only [S, X] using
      (holomorphicFamily_restrictionClosure_compact
        (fun k => F (φ k)) U hU (fun k => hF (φ k))
        (fun K hK hKU => by
          obtain ⟨C, hC⟩ := hbounded K hK hKU
          exact ⟨C, fun k => hC (φ k)⟩)
        (E.sets n) (E.isCompact n) (E.subset n))
  let P : Set (∀ n, X n) := Set.univ.pi S
  have hP : IsCompact P := by
    simpa only [P] using isCompact_univ_pi hS
  let x : ℕ → ∀ n, X n := fun k n =>
    UniformFun.ofFun (fun z : E.sets n => F (φ k) z)
  have hx : ∀ k, x k ∈ P := by
    intro k n _hn
    exact subset_closure ⟨k, rfl⟩
  obtain ⟨a, ha, ψ, hψ, hlim⟩ := hP.tendsto_subseq hx
  have hcoord : ∀ n, TendstoUniformly
      (fun k (z : E.sets n) => F (φ (ψ k)) z)
      (fun z => a n z) atTop := by
    intro n
    have hn : Tendsto (fun k => x (ψ k) n) atTop (nhds (a n)) :=
      (tendsto_pi_nhds.mp hlim) n
    have hu := UniformFun.tendsto_iff_tendstoUniformly.mp hn
    simpa only [x, Function.comp_apply] using hu
  let pick : ∀ z : ℂ, z ∈ U → ℕ := fun z hz =>
    Classical.choose (E.cofinal {z} isCompact_singleton (by simpa using hz))
  have hpick : ∀ (z : ℂ) (hz : z ∈ U), z ∈ E.sets (pick z hz) := by
    intro z hz
    exact Classical.choose_spec
      (E.cofinal {z} isCompact_singleton (by simpa using hz)) (by simp)
  let g : ℂ → ℂ := fun z => if hz : z ∈ U then
    a (pick z hz) ⟨z, hpick z hz⟩ else 0
  have hg_coord : ∀ n z (hz : z ∈ E.sets n), g z = a n ⟨z, hz⟩ := by
    intro n z hz
    have hzU : z ∈ U := E.subset n hz
    simp only [g, dif_pos hzU]
    have hp := (hcoord (pick z hzU)).tendsto_at ⟨z, hpick z hzU⟩
    have hn := (hcoord n).tendsto_at ⟨z, hz⟩
    apply tendsto_nhds_unique
      (show Tendsto (fun k => F (φ (ψ k)) z) atTop
        (nhds (a (pick z hzU) ⟨z, hpick z hzU⟩)) by simpa using hp)
    exact (show Tendsto (fun k => F (φ (ψ k)) z) atTop
      (nhds (a n ⟨z, hz⟩)) by simpa using hn)
  refine ⟨ψ, hψ, g, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨n, hKn⟩ := E.cofinal K hK hKU
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hevent := (Metric.tendstoUniformly_iff.mp (hcoord n)) epsilon hepsilon
  filter_upwards [hevent] with k hk
  intro z hz
  rw [hg_coord n z (hKn hz)]
  exact hk ⟨z, hKn hz⟩


end StatMech.FrontierA
