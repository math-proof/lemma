/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tfe_threeMeetBox_of_top (ω : ConfigSpace (Sym2 (Site d)))
    (htop : numInfiniteClusters d ω = ⊤) :
    ∃ n : ℕ, ω ∈ threeMeetBox d n := by
  have hmem : ω ∈ ⋃ n, threeMeetBox d n :=
    iEqTop_subset_iUnion_threeMeetBox (by simpa using htop)
  rwa [Set.mem_iUnion] at hmem


theorem tfe_three_distinct_infinite_of_box {n : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁ x₂ x₃ : Site d, (x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n) ∧
      ((cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite) ∧
      (cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
        cluster d ω x₂ ≠ cluster d ω x₃) := by
  obtain ⟨_, x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  exact ⟨x₁, x₂, x₃, ⟨hb1, hb2, hb3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩


theorem tfe_modification_preserves_distinct (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d) (R₁ R₂ R₃ : Set (Site d))
    (hm1 : a₁ ∈ R₁) (hm2 : a₂ ∈ R₂) (hm3 : a₃ ∈ R₃)
    (ho1 : ∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁)
    (ho2 : ∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂)
    (ho3 : ∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)
    (hg1 : ∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁)
    (hg2 : ∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂)
    (hg3 : ∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)
    (hd12 : Disjoint R₁ R₂) (hd13 : Disjoint R₁ R₃) (hd23 : Disjoint R₂ R₃) :
    (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₂) ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₂
        ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) :=
  ⟨tre_branch_distinct_of_regions ω W a₁ a₂ R₁ R₂ hm1 hm2 ho1 hg1 ho2 hg2 hd12,
    tre_branch_distinct_of_regions ω W a₁ a₃ R₁ R₃ hm1 hm3 ho1 hg1 ho3 hg3 hd13,
    tre_branch_distinct_of_regions ω W a₂ a₃ R₂ R₃ hm2 hm3 ho2 hg2 ho3 hg3 hd23⟩


theorem tfe_threeClustersReachOrigin_of_attach (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ hd h


end Percolation
end StatMech
