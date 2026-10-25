/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc94density.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Def.StatisticalMechanics.Code.Walls.bc95forestdensity.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc95_density_of_singleSiteRewiring (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hrw : bc95_SingleSiteRewiring μ) : bc94_GenuineTrifExistence μ := by
  intro hpos
  obtain ⟨A, hApos, hAsub⟩ := hrw hpos
  exact lt_of_lt_of_le hApos (measure_mono hAsub)


theorem bc95_bk_from_residues (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
    (hrw : bc95_SingleSiteRewiring μ) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc94_bk_from_density μ hprob0 (bc95_density_of_singleSiteRewiring μ hrw)


theorem bc95_perConfig_contrast {V : Type*} [Fintype V] (G : SimpleGraph V)
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) :
    
    (∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧ (∀ {u v : V}, G.Reachable u v → F.Reachable u v)) ∧
    
    ((∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x) →
     (∀ x, x ∈ box d n → IsTrifurcation d ω x →
       ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) →
     (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) →
     bst_BoxOpenForest ω n) := by
  refine ⟨bc95_spanForest_exists G, ?_⟩
  intro hcanon harmbox hexists
  exact bc95_boxOpenForest_of_harmbox ω n hn hcanon harmbox hexists


theorem bc95_upperLines_zero_density (n : ℕ) :
    bc89_genuineTcount bc60_upperLines n = 0 ∧
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  ⟨bc89_upperLines_genuineTcount_zero n, bc85_upperLines_N_top⟩


theorem bc95_status :
    
    (∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
        (∀ {u v : V}, G.Reachable u v → F.Reachable u v)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
        ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) →
      (∃ x, x ∈ box 2 n ∧ IsTrifurcation 2 ω x) →
      bst_BoxOpenForest ω n) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), bc95_AeArmReaching μ →
      ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, bst_BoxOpenForest ω n) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), bc95_SingleSiteRewiring μ →
      bc94_GenuineTrifExistence μ) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → bc95_SingleSiteRewiring μ →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    
    (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0 ∧
      numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V _ G; exact bc95_spanForest_exists G
  · intro ω n hn hcanon harmbox hexists; exact bc95_boxOpenForest_of_harmbox ω n hn hcanon harmbox hexists
  · intro μ hres n hn; exact bc95_forestResidue_of_ae_armReaching μ hres n hn
  · intro μ hrw; exact bc95_density_of_singleSiteRewiring μ hrw
  · intro μ _ hprob0 hrw; exact bc95_bk_from_residues μ hprob0 hrw
  · intro n; exact bc95_upperLines_zero_density n

end StatMech.Walls
