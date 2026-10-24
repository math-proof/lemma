import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wdcdartconnected
open SimpleGraph Function StatMech StatMech.Wots


/--
[wdc_layer_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_layer_not_mem_eq
  {K : Set (Site 2)}
  {v : Site 2}
-- given
  (hv : v ∈ wdc_boundaryLayer K) :
-- imply
  v ∉ K := by
-- proof
  apply StatMech.Wots.wdc_layer_not_mem hv

/--
[wdc_head_mem_layer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_head_mem_layer_eq
  {K : Set (Site 2)}
  {d : {e : Dart // IsBoundaryDart K e}} :
-- imply
  d.1.head ∈ wdc_boundaryLayer K := by
-- proof
  apply StatMech.Wots.wdc_head_mem_layer K d

/--
[wdc_layer_isHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_layer_isHead_eq
  {K : Set (Site 2)}
  {v : Site 2}
-- given
  (hv : v ∈ wdc_boundaryLayer K) :
-- imply
  ∃ d : {e : Dart // IsBoundaryDart K e}, d.1.head = v := by
-- proof
  apply StatMech.Wots.wdc_layer_isHead K hv

/--
[wdc_layerGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_layerGraph_adj_eq
  {K : Set (Site 2)}
-- given
  (a b : {v : Site 2 // v ∈ wdc_boundaryLayer K}) :
-- imply
  (wdc_layerGraph K).Adj a b ↔ KingAdj (a : Site 2) (b : Site 2) ∧ ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ := by
-- proof
  apply StatMech.Wots.wdc_layerGraph_adj K a b

/--
[wdc_wots_adj_of_kingAdj_heads](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_wots_adj_of_kingAdj_heads_eq
  {K : Set (Site 2)}
  {d1 d2 : {e : Dart // IsBoundaryDart K e}}
-- given
  (hk : KingAdj d1.1.head d2.1.head)
  (hr : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩) :
-- imply
  (wots_dartGraph K).Adj d1 d2 := by
-- proof
  apply StatMech.Wots.wdc_wots_adj_of_kingAdj_heads K d1 d2 hk hr

/--
[wdc_wots_adj_of_eq_heads](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_wots_adj_of_eq_heads_eq
  {K : Set (Site 2)}
  {d1 d2 : {e : Dart // IsBoundaryDart K e}}
-- given
  (hne : d1 ≠ d2)
  (heq : d1.1.head = d2.1.head) :
-- imply
  (wots_dartGraph K).Adj d1 d2 := by
-- proof
  apply StatMech.Wots.wdc_wots_adj_of_eq_heads K d1 d2 hne heq

/--
[wdc_pick_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_pick_head_eq
  {K : Set (Site 2)}
-- given
  (v : {x : Site 2 // x ∈ wdc_boundaryLayer K}) :
-- imply
  (wdc_pick K v).1.head = v.1 := by
-- proof
  apply StatMech.Wots.wdc_pick_head K v

/--
[wdc_pick_reachable_of_layerReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_pick_reachable_of_layerReachable_eq
  {K : Set (Site 2)}
  {a b : {x : Site 2 // x ∈ wdc_boundaryLayer K}}
-- given
  (h : (wdc_layerGraph K).Reachable a b) :
-- imply
  (wots_dartGraph K).Reachable (wdc_pick K a) (wdc_pick K b) := by
-- proof
  apply StatMech.Wots.wdc_pick_reachable_of_layerReachable K h

/--
[wdc_dartConnected_of_layerConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean)
-/
@[path]
private lemma wdc_dartConnected_of_layerConnected_eq
  {K : Set (Site 2)}
-- given
  (h : wdc_LayerConnected K) :
-- imply
  wots_DartConnected K := by
-- proof
  apply StatMech.Wots.wdc_dartConnected_of_layerConnected K h


-- created on 2026-10-23
