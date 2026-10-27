import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc94density.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc94_genuineTcount_le_boundary_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_genuineTcount_le_boundary_of_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bst_BoxOpenForest ω n) :
-- imply
  bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc94_genuineTcount_le_boundary_of_forest ω n h

/--
[bc94_genuineTcount_le_boundary_of_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_genuineTcount_le_boundary_of_inputs_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc94_genuineTcount_le_boundary_of_inputs ω n hn hcanon harmbox

/--
[bc94_count_bound_under_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_count_bound_under_top_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (_hN : numInfiniteClusters d ω = ⊤)
  (h : bst_BoxOpenForest ω n) :
-- imply
  bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc94_count_bound_under_top ω n _hN h

/--
[bc94_count_bound_under_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_count_bound_under_ge_two_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (_hN : 2 ≤ numInfiniteClusters d ω)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc94_count_bound_under_ge_two ω n hn _hN hcanon harmbox

/--
[bc94_ae_genuineCount_bound_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_ae_genuineCount_bound_of_residue_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {n : ℕ}
-- given
  (hres : bc94_DensityForestResidue μ) :
-- imply
  ∀ᵐ ω ∂μ, bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc94_ae_genuineCount_bound_of_residue μ hres n

/--
[bc94_upperLines_zero_density_and_N_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_upperLines_zero_density_and_N_top_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc89_genuineTcount bc60_upperLines n = 0 ∧ numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc94_upperLines_zero_density_and_N_top n

/--
[bc94_forward_density_uses_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_forward_density_uses_top_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hexist : bc94_GenuineTrifExistence μ)
  (hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤}) :
-- imply
  0 < μ {ω | bc89_GenuineTrif d ω 0} := by
-- proof
  apply StatMech.Walls.bc94_forward_density_uses_top μ hexist hpos

/--
[bc94_exclude_top_of_density](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_exclude_top_of_density_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
  (hexist : bc94_GenuineTrifExistence μ) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc94_exclude_top_of_density μ hprob0 hexist

/--
[bc94_bk_from_density](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_bk_from_density_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
  (hexist : bc94_GenuineTrifExistence μ) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc94_bk_from_density μ hprob0 hexist

/--
[bc94_circularity_contrast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_circularity_contrast_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L n : ℕ} :
-- imply
  ((numInfiniteClusters d ω ≤ 1 → ∀ y', ¬ bc93_BadBox ω L y') ∧ (∀ y', bc93_BadBox ω L y' → 2 ≤ numInfiniteClusters d ω)) ∧ (numInfiniteClusters d ω = ⊤ → bst_BoxOpenForest ω n → bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n) := by
-- proof
  apply StatMech.Walls.bc94_circularity_contrast ω L n

/--
[bc94_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc94density.lean)
-/
@[path]
private lemma bc94_status_eq
  {d : ℕ} :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))), bc94_GenuineTrifExistence μ → 0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → 0 < μ {ω | bc89_GenuineTrif 2 ω 0}) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), numInfiniteClusters 2 ω = ⊤ → bst_BoxOpenForest ω n → bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) → (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) → bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → bc94_GenuineTrifExistence μ → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L n : ℕ), ((numInfiniteClusters 2 ω ≤ 1 → ∀ y', ¬ bc93_BadBox ω L y') ∧ (∀ y', bc93_BadBox ω L y' → 2 ≤ numInfiniteClusters 2 ω)) ∧ (numInfiniteClusters 2 ω = ⊤ → bst_BoxOpenForest ω n → bc89_genuineTcount ω n ≤ boxSV_boundaryCard 2 n)) ∧ (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0 ∧ numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc94_status


-- created on 2026-10-23
