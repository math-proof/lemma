import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[str_spider_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_adj_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {a b : str_SpiderV N} :
-- imply
  (str_spiderG N).Adj a b ↔ a ≠ b ∧ (str_sAdj a b = true ∨ str_sAdj b a = true) := by
-- proof
  apply StatMech.Percolation.str_spider_adj a b

/--
[str_spider_reach_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_reach_root_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {v : str_SpiderV N} :
-- imply
  (str_spiderG N).Reachable none v := by
-- proof
  apply StatMech.Percolation.str_spider_reach_root v

/--
[str_spiderG_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spiderG_connected_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N] :
-- imply
  (str_spiderG N).Connected := by
-- proof
  apply StatMech.Percolation.str_spiderG_connected

/--
[str_spider_leaf_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_leaf_deg_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {p : N × Fin 2} :
-- imply
  (str_spiderG N).degree (some (Sum.inr p)) = 1 := by
-- proof
  apply StatMech.Percolation.str_spider_leaf_deg p

/--
[str_spider_hub_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_hub_deg_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {i : N} :
-- imply
  (str_spiderG N).degree (some (Sum.inl i)) = 3 := by
-- proof
  apply StatMech.Percolation.str_spider_hub_deg i

/--
[str_spider_root_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_root_deg_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N] :
-- imply
  (str_spiderG N).degree none = Fintype.card N := by
-- proof
  apply StatMech.Percolation.str_spider_root_deg

/--
[str_spider_sum_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_sum_deg_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N] :
-- imply
  ∑ v, (str_spiderG N).degree v = 6 * Fintype.card N := by
-- proof
  apply StatMech.Percolation.str_spider_sum_deg

/--
[str_spider_card_V](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_card_V_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N] :
-- imply
  Fintype.card (str_SpiderV N) = 1 + 3 * Fintype.card N := by
-- proof
  apply StatMech.Percolation.str_spider_card_V

/--
[str_spider_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_edge_card_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N] :
-- imply
  (str_spiderG N).edgeFinset.card = 3 * Fintype.card N := by
-- proof
  apply StatMech.Percolation.str_spider_edge_card

/--
[str_spiderG_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spiderG_isTree_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N] :
-- imply
  (str_spiderG N).IsTree := by
-- proof
  apply StatMech.Percolation.str_spiderG_isTree

/--
[str_spider_two_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_two_le_card_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
-- given
  (hN : 1 ≤ Fintype.card N) :
-- imply
  2 ≤ Fintype.card (str_SpiderV N) := by
-- proof
  apply StatMech.Percolation.str_spider_two_le_card hN

/--
[str_spider_leaf_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spider_leaf_cases_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {v : str_SpiderV N}
-- given
  (hv : (str_spiderG N).degree v = 1) :
-- imply
  v = none ∨ ∃ p, v = some (Sum.inr p) := by
-- proof
  apply StatMech.Percolation.str_spider_leaf_cases v hv

/--
[str_spanningTreeLeafCount_of_forestLeafSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spanningTreeLeafCount_of_forestLeafSelection_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : str_ForestLeafSelection ω n)
  (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
-- imply
  flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.str_spanningTreeLeafCount_of_forestLeafSelection ω n h hbase

/--
[str_forestLeafSelection_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_forestLeafSelection_star_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {r a₀ a₁ r₀ : Site d}
-- given
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r)
  (_hrbox : r ∈ box d n)
  (_htri_r : IsTrifurcation d ω r)
  (ha₀ : a₀ ∈ vertexBoundary d n)
  (ha₁ : a₁ ∈ vertexBoundary d n)
  (hr₀ : r₀ ∈ vertexBoundary d n)
  (hc₀ : Connected d ω r a₀)
  (hc₁ : Connected d ω r a₁)
  (hdistinct : a₀ ≠ a₁ ∧ a₀ ≠ r₀ ∧ a₁ ≠ r₀) :
-- imply
  str_ForestLeafSelection ω n := by
-- proof
  apply StatMech.Percolation.str_forestLeafSelection_star ω n hsingle _hrbox _htri_r ha₀ ha₁ hr₀ hc₀ hc₁ hdistinct

/--
[str_forestLeafSelection_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_forestLeafSelection_of_data_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {r₀ : Site d}
  {ℓ : Site d → Fin 2 → Site d}
-- given
  (hr₀ : r₀ ∈ vertexBoundary d n)
  (hℓbdry : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, ℓ x j ∈ vertexBoundary d n)
  (hℓconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, Connected d ω x (ℓ x j))
  (hℓr₀ : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, ℓ x j ≠ r₀)
  (hℓinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → ∀ j j', ℓ x j = ℓ y j' → x = y ∧ j = j') :
-- imply
  str_ForestLeafSelection ω n := by
-- proof
  apply StatMech.Percolation.str_forestLeafSelection_of_data ω n r₀ ℓ hr₀ hℓbdry hℓconn hℓr₀ hℓinj

/--
[str_base_of_twoBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_base_of_twoBoundary_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d n)
  (hz₁ : z₁ ∈ vertexBoundary d n)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.str_base_of_twoBoundary ω n hz₀ hz₁ hzne hno

/--
[str_Tcount_le_boundary_of_forestLeafSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_Tcount_le_boundary_of_forestLeafSelection_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : str_ForestLeafSelection ω n)
  (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.str_Tcount_le_boundary_of_forestLeafSelection ω n h hbase

/--
[str_spanningTree_of_forestLeafSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_spanningTree_of_forestLeafSelection_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
-- given
  (hsel : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → str_ForestLeafSelection ω n)
  (hbase : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
-- imply
  ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.str_spanningTree_of_forestLeafSelection hsel hbase

/--
[str_burton_keane_bernoulli_of_forestLeafSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean)
-/
@[path]
private lemma str_burton_keane_bernoulli_of_forestLeafSelection_eq
  {d : ℕ}
  [Fintype N]
  [DecidableEq N]
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hsel : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → str_ForestLeafSelection ω n)
  (hbase : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.str_burton_keane_bernoulli_of_forestLeafSelection hd p hp1 hp0 hsel hbase htrif


-- created on 2026-10-23
