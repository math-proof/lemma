import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.ForestLeafCountClose
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation StatMech.Percolation.Flc2Witness


/--
[flc2_deg_pos_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_deg_pos_of_connected_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
-- given
  (hconn : G.Connected)
  (hV : 2 ≤ Fintype.card V) :
-- imply
  1 ≤ G.degree v := by
-- proof
  apply StatMech.Percolation.flc2_deg_pos_of_connected G hconn hV v

/--
[flc2_tree_internal_lt_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_tree_internal_lt_leaves_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hT : G.IsTree)
  (hV : 2 ≤ Fintype.card V) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card < (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Percolation.flc2_tree_internal_lt_leaves G hT hV

/--
[flc2_trifImage_card_le_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_trifImage_card_le_deg3_eq
  {d : ℕ}
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {Tw : Finset W}
-- given
  (hTw : ∀ w ∈ Tw, 3 ≤ G.degree w) :
-- imply
  Tw.card ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := by
-- proof
  apply StatMech.Percolation.flc2_trifImage_card_le_deg3 G Tw hTw

/--
[flc2_leaf_card_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_leaf_card_le_boundary_eq
  {d : ℕ}
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {n : ℕ}
  {lam : W → Site d}
-- given
  (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d n)
  (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
-- imply
  (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.flc2_leaf_card_le_boundary G n lam hmap hinj

/--
[flc2_Tcount_le_boundary_of_spanningTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_Tcount_le_boundary_of_spanningTree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : flc2_SpanningTreeLeafCount ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.flc2_Tcount_le_boundary_of_spanningTree ω n h

/--
[flc2_forest_component_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_forest_component_card_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
-- given
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  ∃ w, G.Adj v w := by
-- proof
  apply StatMech.Percolation.flc2_forest_component_card G hmin v

/--
[flc2_forest_internal_le_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_forest_internal_le_leaves_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Percolation.flc2_forest_internal_le_leaves G hacyc hmin

/--
[pathG_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma pathG_isTree_eq
  {d : ℕ} :
-- imply
  pathG.IsTree := by
-- proof
  apply StatMech.Percolation.Flc2Witness.pathG_isTree

/--
[pathG_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma pathG_deg_eq
  {d : ℕ}
  {v : Fin 2} :
-- imply
  pathG.degree v = 1 := by
-- proof
  apply StatMech.Percolation.Flc2Witness.pathG_deg v

/--
[starG_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma starG_isTree_eq
  {d : ℕ} :
-- imply
  starG.IsTree := by
-- proof
  apply StatMech.Percolation.Flc2Witness.starG_isTree

/--
[starG_centre_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma starG_centre_deg_eq
  {d : ℕ} :
-- imply
  starG.degree 0 = 3 := by
-- proof
  apply StatMech.Percolation.Flc2Witness.starG_centre_deg

/--
[starG_leaf_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma starG_leaf_deg_eq
  {d : ℕ} :
-- imply
  ∀ v : Fin 4, v ≠ 0 → starG.degree v = 1 := by
-- proof
  apply StatMech.Percolation.Flc2Witness.starG_leaf_deg

/--
[starG_deg1_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma starG_deg1_iff_eq
  {d : ℕ}
  {v : Fin 4} :
-- imply
  starG.degree v = 1 ↔ v ≠ 0 := by
-- proof
  apply StatMech.Percolation.Flc2Witness.starG_deg1_iff v

/--
[flc2_spanningTreeLeafCount_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_spanningTreeLeafCount_of_noTrif_eq
  {d : ℕ}
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
  apply StatMech.Percolation.flc2_spanningTreeLeafCount_of_noTrif ω n hz₀ hz₁ hzne hno

/--
[flc2_spanningTreeLeafCount_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_spanningTreeLeafCount_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {r : Site d}
  {z : Fin 3 → Site d}
-- given
  (hrbox : r ∈ box d n)
  (htri_r : IsTrifurcation d ω r)
  (hzb : ∀ i, z i ∈ vertexBoundary d n)
  (hzinj : Function.Injective z)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r) :
-- imply
  flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.flc2_spanningTreeLeafCount_star ω n hrbox htri_r z hzb hzinj hsingle

/--
[flc2_hbound_of_spanningTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_hbound_of_spanningTree_eq
  {d : ℕ}
-- given
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n) :
-- imply
  ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.flc2_hbound_of_spanningTree hres

/--
[flc2_burton_keane_bernoulli_of_spanningTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean)
-/
@[path]
private lemma flc2_burton_keane_bernoulli_of_spanningTree_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.flc2_burton_keane_bernoulli_of_spanningTree hd p hp1 hp0 hres htrif


-- created on 2026-10-23
