/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc122carrier.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bgf_targets_sep_of_arms_sep (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {aᵢ aⱼ zᵢ zⱼ : Site d}
    (hri : (bc67_contractedLattice ω L y).Reachable aᵢ zᵢ)
    (hrj : (bc67_contractedLattice ω L y).Reachable aⱼ zⱼ)
    (hcut : ¬ (bc67_contractedLattice ω L y).Reachable aᵢ aⱼ) :
    ¬ (bc67_contractedLattice ω L y).Reachable zᵢ zⱼ := by
  intro hz
  exact hcut (hri.trans (hz.trans hrj.symm))


theorem bgf_three_targets_separated (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {a₁ a₂ a₃ z₁ z₂ z₃ : Site d}
    (hr₁ : (bc67_contractedLattice ω L y).Reachable a₁ z₁)
    (hr₂ : (bc67_contractedLattice ω L y).Reachable a₂ z₂)
    (hr₃ : (bc67_contractedLattice ω L y).Reachable a₃ z₃)
    (hc₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
    (hc₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
    (hc₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
    ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧
    ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧
    ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃ :=
  ⟨bgf_targets_sep_of_arms_sep ω L y hr₁ hr₂ hc₁₂,
   bgf_targets_sep_of_arms_sep ω L y hr₁ hr₃ hc₁₃,
   bgf_targets_sep_of_arms_sep ω L y hr₂ hr₃ hc₂₃⟩


theorem bgf_boundary_targets_distinct (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {z₁ z₂ z₃ : Site d}
    (hs₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂)
    (hs₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃)
    (hs₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) :
    z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ :=
  ⟨fun h => hs₁₂ (h ▸ Reachable.refl _),
   fun h => hs₁₃ (h ▸ Reachable.refl _),
   fun h => hs₂₃ (h ▸ Reachable.refl _)⟩


theorem bgf_gnTrif_three_boundary_targets (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a₁ a₂ a₃ : Site d)
    (hb₁ : a₁ ∈ box d R) (hb₂ : a₂ ∈ box d R) (hb₃ : a₃ ∈ box d R)
    (hi₁ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite)
    (hi₂ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite)
    (hi₃ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite)
    (hc₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
    (hc₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
    (hc₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
    ∃ z₁ z₂ z₃ : Site d,
      (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧
      ((bc67_contractedLattice ω L y).Reachable a₁ z₁ ∧
       (bc67_contractedLattice ω L y).Reachable a₂ z₂ ∧
       (bc67_contractedLattice ω L y).Reachable a₃ z₃) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨z₁, hzb₁, hr₁⟩ := bc101_arm_reaches_boundary ω L R hR y a₁ hb₁ hi₁
  obtain ⟨z₂, hzb₂, hr₂⟩ := bc101_arm_reaches_boundary ω L R hR y a₂ hb₂ hi₂
  obtain ⟨z₃, hzb₃, hr₃⟩ := bc101_arm_reaches_boundary ω L R hR y a₃ hb₃ hi₃
  have hsep := bgf_three_targets_separated ω L y hr₁ hr₂ hr₃ hc₁₂ hc₁₃ hc₂₃
  exact ⟨z₁, z₂, z₃, ⟨hzb₁, hzb₂, hzb₃⟩, ⟨hr₁, hr₂, hr₃⟩, hsep,
    bgf_boundary_targets_distinct ω L y hsep.1 hsep.2.1 hsep.2.2⟩


theorem bgf_arm_boundary_separated (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y : Site d) (htri : bc67_IsGnTrifurcation ω L y)
    (harmbox : ∀ a, (bc67_GnIncident ω L y a) →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → a ∈ box d R) :
    ∃ z₁ z₂ z₃ : Site d,
      (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨a₁, a₂, a₃, ⟨hin₁, hin₂, hin₃⟩, ⟨hi₁, hi₂, hi₃⟩, hc₁₂, hc₁₃, hc₂₃⟩ := htri
  obtain ⟨z₁, z₂, z₃, hzb, _hr, hsep, hdist⟩ :=
    bgf_gnTrif_three_boundary_targets ω L R hR y a₁ a₂ a₃
      (harmbox a₁ hin₁ hi₁) (harmbox a₂ hin₂ hi₂) (harmbox a₃ hin₃ hi₃)
      hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃
  exact ⟨z₁, z₂, z₃, hzb, hsep, hdist⟩


end StatMech.Walls
