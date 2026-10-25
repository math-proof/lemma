/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.GenuineEdgeCollapse
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.AdditiveGluing.Part5
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]


theorem agl_right_block_fkZ_eq (N m : ℕ) (P : boxVerts d N → Prop) [DecidablePred P]
    (v : Site d) (φ : boxVerts d m ≃ {x // ¬ P x})
    (hφ : ∀ y : boxVerts d m, ((φ y : boxVerts d N) : Site d) = (y : Site d) + v) (p q : ℝ) :
    fkZ (agl_right (boxGraph d N) P) p q = fkZ (boxGraph d m) p q :=
  (fsm_fkZ_iso (boxGraph d m) (agl_right (boxGraph d N) P)
    (agl_rightBlockIso N m P v φ hφ) p q).symm


theorem agl_subseq_almost_mono_converges (g : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 ≤ δ j) (hsum : Summable δ)
    (hmono : ∀ j, g (K j) - δ j ≤ g (K (j + 1)))
    (hbdd : BddAbove (Set.range fun j => g (K j))) :
    ∃ L, Tendsto (fun j => g (K j)) atTop (𝓝 L) :=
  bpv_almost_mono_converges (fun j => g (K j)) δ hδ hsum hmono hbdd


theorem agl_full_from_subseq (g : ℕ → ℝ) (K : ℕ → ℕ) (L : ℝ)
    (hsub : Tendsto (fun j => g (K j)) atTop (𝓝 L))
    (bj : ℕ → ℕ) (hbj : Tendsto bj atTop atTop)
    (osc : ℕ → ℝ) (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, |g n - g (K (bj n))| ≤ osc (bj n)) :
    Tendsto g atTop (𝓝 L) := by
  have hcomp : Tendsto (fun n => g (K (bj n))) atTop (𝓝 L) := hsub.comp hbj
  have hosc' : Tendsto (fun n => osc (bj n)) atTop (𝓝 0) := hosc.comp hbj
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hcomp) (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hosc') (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hnN1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hnN2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  have hd1 : dist (g (K (bj n))) L < ε / 2 := hN1 n hnN1
  have hd2 : dist (osc (bj n)) 0 < ε / 2 := hN2 n hnN2
  have hsd : |g n - g (K (bj n))| ≤ osc (bj n) := hsand n
  have hoscnn : 0 ≤ osc (bj n) := le_trans (abs_nonneg _) hsd
  rw [Real.dist_eq] at hd1 hd2 ⊢
  rw [sub_zero, abs_of_nonneg hoscnn] at hd2
  calc |g n - L| = |(g n - g (K (bj n))) + (g (K (bj n)) - L)| := by ring_nf
    _ ≤ |g n - g (K (bj n))| + |g (K (bj n)) - L| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add_of_le_of_lt
        · exact le_trans hsd (le_of_lt hd2)
        · exact hd1
    _ = ε := by ring


theorem agl_perVolume_converges (g : ℕ → ℝ) (K : ℕ → ℕ) (δ osc : ℕ → ℝ) (bj : ℕ → ℕ)
    (hδ : ∀ j, 0 ≤ δ j) (hsum : Summable δ)
    (hmono : ∀ j, g (K j) - δ j ≤ g (K (j + 1)))
    (hbdd : BddAbove (Set.range fun j => g (K j)))
    (hbj : Tendsto bj atTop atTop)
    (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, |g n - g (K (bj n))| ≤ osc (bj n)) :
    ∃ L, Tendsto g atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := agl_subseq_almost_mono_converges g K δ hδ hsum hmono hbdd
  exact ⟨L, agl_full_from_subseq g K L hL bj hbj osc hosc hsand⟩


end FK
end StatMech
