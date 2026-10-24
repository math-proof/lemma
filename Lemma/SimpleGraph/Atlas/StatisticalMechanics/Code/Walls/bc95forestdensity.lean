import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc95forestdensity
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc95_spanForest_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_spanForest_exists_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧ (∀ {u v : V}, G.Reachable u v → F.Reachable u v) := by
-- proof
  apply StatMech.Walls.bc95_spanForest_exists G

/--
[bc95_spanForest_degree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_spanForest_degree_pos_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel (osf_spanForest G).Adj]
  {u v : V}
-- given
  (hv : v ≠ u)
  (h : G.Reachable u v) :
-- imply
  1 ≤ (osf_spanForest G).degree u := by
-- proof
  apply StatMech.Walls.bc95_spanForest_degree_pos G hv h

/--
[bc95_boxOpenForest_of_harmbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_boxOpenForest_of_harmbox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
  (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
-- imply
  bst_BoxOpenForest ω n := by
-- proof
  apply StatMech.Walls.bc95_boxOpenForest_of_harmbox ω n hn hcanon harmbox hexists

/--
[bc95_ae_genuineCount_of_armReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_ae_genuineCount_of_armReaching_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {n : ℕ}
-- given
  (hres : bc95_AeArmReaching μ)
  (hn : 1 ≤ n) :
-- imply
  ∀ᵐ ω ∂μ, bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc95_ae_genuineCount_of_armReaching μ hres n hn

/--
[bc95_forestResidue_of_ae_armReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_forestResidue_of_ae_armReaching_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {n : ℕ}
-- given
  (hres : bc95_AeArmReaching μ)
  (hn : 1 ≤ n) :
-- imply
  ∀ᵐ ω ∂μ, bst_BoxOpenForest ω n := by
-- proof
  apply StatMech.Walls.bc95_forestResidue_of_ae_armReaching μ hres n hn

/--
[bc95_density_of_singleSiteRewiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_density_of_singleSiteRewiring_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hrw : bc95_SingleSiteRewiring μ) :
-- imply
  bc94_GenuineTrifExistence μ := by
-- proof
  apply StatMech.Walls.bc95_density_of_singleSiteRewiring μ hrw

/--
[bc95_bk_from_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_bk_from_residues_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
  (hrw : bc95_SingleSiteRewiring μ) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc95_bk_from_residues μ hprob0 hrw

/--
[bc95_perConfig_contrast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_perConfig_contrast_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧ (∀ {u v : V}, G.Reachable u v → F.Reachable u v)) ∧ ((∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x) → (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) → (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) → bst_BoxOpenForest ω n) := by
-- proof
  apply StatMech.Walls.bc95_perConfig_contrast G ω n hn

/--
[bc95_upperLines_zero_density](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_upperLines_zero_density_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc89_genuineTcount bc60_upperLines n = 0 ∧ numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc95_upperLines_zero_density n

/--
[bc95_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean)
-/
@[path]
private lemma bc95_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type*} [Fintype V] (G : SimpleGraph V), ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧ (∀ {u v : V}, G.Reachable u v → F.Reachable u v)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) → (∃ x, x ∈ box 2 n ∧ IsTrifurcation 2 ω x) → bst_BoxOpenForest ω n) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), bc95_AeArmReaching μ → ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, bst_BoxOpenForest ω n) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), bc95_SingleSiteRewiring μ → bc94_GenuineTrifExistence μ) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → bc95_SingleSiteRewiring μ → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0 ∧ numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc95_status


-- created on 2026-10-23
