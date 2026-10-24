import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial
open StatMech StatMech.FrontierA


/--
[kwDartEdgeBitValue_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwDartEdgeBitValue_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
  {d : G.Dart} :
-- imply
  kwDartEdgeBitValue G b d.edge = b.1 d := by
-- proof
  apply StatMech.FrontierA.kwDartEdgeBitValue_edge G b d

/--
[mem_kwDartEdgeBitsFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma mem_kwDartEdgeBitsFinset_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
  {d : G.Dart} :
-- imply
  d.edge ∈ kwDartEdgeBitsFinset G b ↔ b.1 d = 1 := by
-- proof
  apply StatMech.FrontierA.mem_kwDartEdgeBitsFinset_iff G b d

/--
[kwFinsetDartEdgeBits_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwFinsetDartEdgeBits_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {d : G.Dart} :
-- imply
  (kwFinsetDartEdgeBits G F).1 d = (if d.edge ∈ F then 1 else 0) := by
-- proof
  apply StatMech.FrontierA.kwFinsetDartEdgeBits_apply G F d

/--
[kwDartEdgeBitsFinset_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwDartEdgeBitsFinset_finset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  kwDartEdgeBitsFinset G (kwFinsetDartEdgeBits G F) = F := by
-- proof
  apply StatMech.FrontierA.kwDartEdgeBitsFinset_finset G F hF

/--
[kwFinsetDartEdgeBits_bitsFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwFinsetDartEdgeBits_bitsFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G} :
-- imply
  kwFinsetDartEdgeBits G (kwDartEdgeBitsFinset G b) = b := by
-- proof
  apply StatMech.FrontierA.kwFinsetDartEdgeBits_bitsFinset G b

/--
[kw_incidenceFinset_eq_image_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_incidenceFinset_eq_image_neighborFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V} :
-- imply
  G.incidenceFinset v = (G.neighborFinset v).image (fun w => s(v, w)) := by
-- proof
  apply StatMech.FrontierA.kw_incidenceFinset_eq_image_neighborFinset G v

/--
[kw_neighborEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_neighborEdge_injective_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V} :
-- imply
  Set.InjOn (fun w => s(v, w)) (G.neighborSet v) := by
-- proof
  apply StatMech.FrontierA.kw_neighborEdge_injective G v

/--
[kw_incCount_filter_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_incCount_filter_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred Q]
  {v : V}
-- given
  (Q : Sym2 V → Prop) :
-- imply
  incCount (G.edgeFinset.filter Q) v = ((G.incidenceFinset v).filter Q).card := by
-- proof
  apply StatMech.FrontierA.kw_incCount_filter_edgeFinset G Q v

/--
[kw_cast_incCount_filter_eq_neighbor_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_cast_incCount_filter_eq_neighbor_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred Q]
  {v : V}
-- given
  (Q : Sym2 V → Prop) :
-- imply
  ((incCount (G.edgeFinset.filter Q) v : ℕ) : ZMod 2) = ∑ w ∈ G.neighborFinset v, if Q s(v, w) then (1 : ZMod 2) else 0 := by
-- proof
  apply StatMech.FrontierA.kw_cast_incCount_filter_eq_neighbor_sum G Q v

/--
[kw_fin2_indicator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_fin2_indicator_eq_eq
  {a : Fin 2} :
-- imply
  (if a = 1 then (1 : Fin 2) else 0) = a := by
-- proof
  apply StatMech.FrontierA.kw_fin2_indicator_eq a

/--
[kw_zmod2_indicator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_zmod2_indicator_eq_eq
  {a : Fin 2} :
-- imply
  (if a = 1 then (1 : ZMod 2) else 0) = a := by
-- proof
  apply StatMech.FrontierA.kw_zmod2_indicator_eq a

/--
[kw_externalPortBits_sum_eq_neighbor_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_externalPortBits_sum_eq_neighbor_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
  {v : V} :
-- imply
  (∑ i : Fin (Fintype.card (KWOutgoingDart (G := G) v)), kwExternalPortBits G b ⟨v, i⟩) = ∑ w ∈ G.neighborFinset v, kwDartEdgeBitValue G b s(v, w) := by
-- proof
  apply StatMech.FrontierA.kw_externalPortBits_sum_eq_neighbor_sum G b v

/--
[kwDartEdgeBitsFinset_even_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwDartEdgeBitsFinset_even_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G} :
-- imply
  IsEvenSubgraph (kwDartEdgeBitsFinset G b) ↔ KWOriginalPortEven G b := by
-- proof
  apply StatMech.FrontierA.kwDartEdgeBitsFinset_even_iff G b

/--
[mem_kwOrderedInternalNeighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma mem_kwOrderedInternalNeighborFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p q : KWDartPort G} :
-- imply
  q ∈ kwOrderedInternalNeighborFinset G order p ↔ p.1 = q.1 ∧ (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨ kwOrderedPortRank order q + 1 = kwOrderedPortRank order p) := by
-- proof
  apply StatMech.FrontierA.mem_kwOrderedInternalNeighborFinset G order p q

/--
[kwDartOfPort_matchingNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwDartOfPort_matchingNeighbor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : KWDartPort G} :
-- imply
  kwDartOfPort G (kwOrderedMatchingNeighbor G p) = (kwDartOfPort G p).symm := by
-- proof
  apply StatMech.FrontierA.kwDartOfPort_matchingNeighbor G p

/--
[kwOrderedMatchingNeighbor_not_mem_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedMatchingNeighbor_not_mem_internal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p : KWDartPort G} :
-- imply
  kwOrderedMatchingNeighbor G p ∉ kwOrderedInternalNeighborFinset G order p := by
-- proof
  apply StatMech.FrontierA.kwOrderedMatchingNeighbor_not_mem_internal G order p

/--
[kwOrderedSplit_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplit_neighborFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p : KWDartPort G} :
-- imply
  (kwOrderedDartPortSplitGraph G order).neighborFinset p = insert (kwOrderedMatchingNeighbor G p) (kwOrderedInternalNeighborFinset G order p) := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplit_neighborFinset G order p

/--
[kwOrderedSplitEdgeBitValue_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitEdgeBitValue_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {d : (kwOrderedDartPortSplitGraph G order).Dart} :
-- imply
  kwOrderedSplitEdgeBitValue G order b y d.edge = kwOrderedPortSplitAdjBit G order b y d.fst d.snd := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitEdgeBitValue_edge G order b y d

/--
[mem_kwOrderedSplitEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma mem_kwOrderedSplitEdges_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {d : (kwOrderedDartPortSplitGraph G order).Dart} :
-- imply
  d.edge ∈ kwOrderedSplitEdges G order b y ↔ kwOrderedPortSplitAdjBit G order b y d.fst d.snd = 1 := by
-- proof
  apply StatMech.FrontierA.mem_kwOrderedSplitEdges_iff G order b y d

/--
[kw_fin_sum_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_fin_sum_adjacent_eq
  {n : ℕ}
  {i : Fin n}
  {left right : Fin 2} :
-- imply
  (∑ j ∈ (Finset.univ.filter fun j : Fin n => i.val + 1 = j.val ∨ j.val + 1 = i.val), if j.val + 1 = i.val then left else right) = (if i.val = 0 then 0 else left) + (if i.val + 1 = n then 0 else right) := by
-- proof
  apply StatMech.FrontierA.kw_fin_sum_adjacent i left right

/--
[kwOrderedInternalNeighborFinset_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedInternalNeighborFinset_eq_image_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p : KWDartPort G} :
-- imply
  kwOrderedInternalNeighborFinset G order p = (Finset.univ.filter fun j : Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) => kwOrderedPortRank order p + 1 = j.val ∨ j.val + 1 = kwOrderedPortRank order p).image (kwPortAtOrderedRank order p.1) := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalNeighborFinset_eq_image G order p

/--
[kwPortAtOrderedRank_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwPortAtOrderedRank_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {v : V} :
-- imply
  Function.Injective (kwPortAtOrderedRank order v) := by
-- proof
  apply StatMech.FrontierA.kwPortAtOrderedRank_injective order v

/--
[kwOrderedInternalNeighbor_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedInternalNeighbor_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {p : KWDartPort G} :
-- imply
  (∑ q ∈ kwOrderedInternalNeighborFinset G order p, kwOrderedPortSplitAdjBit G order b y p q) = (if kwOrderedPortRank order p = 0 then 0 else y p.1 (order p.1 p.2).castSucc) + (if kwOrderedPortRank order p + 1 = Fintype.card (KWOutgoingDart (G := G) p.1) then 0 else y p.1 (order p.1 p.2).succ) := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalNeighbor_sum G order b y p

/--
[kwOrderedPortSplitAdjBit_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedPortSplitAdjBit_matching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {p : KWDartPort G} :
-- imply
  kwOrderedPortSplitAdjBit G order b y p (kwOrderedMatchingNeighbor G p) = kwExternalPortBits G b p := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortSplitAdjBit_matching G order b y p

/--
[kwOrderedPortSplit_neighbor_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedPortSplit_neighbor_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {p : KWDartPort G} :
-- imply
  (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p, kwOrderedPortSplitAdjBit G order b y p q) = kwOrderedPortSplitIncidence G order b y p := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortSplit_neighbor_sum G order b y p

/--
[kwOrderedSplitEdges_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitEdges_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
-- given
  (hy : KWOrderedGlobalPortChainEven G order b y) :
-- imply
  kwOrderedSplitEdges G order b y ∈ evenSubgraphs (kwOrderedDartPortSplitGraph G order) := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitEdges_even G order b y hy

/--
[kwOrderedSplitFinsetChainField_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitFinsetChainField_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {F : Finset (Sym2 (KWDartPort G))}
  {v : V} :
-- imply
  kwOrderedSplitFinsetChainField G order F v 0 = 0 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitFinsetChainField_zero G order F v

/--
[kwOrderedSplitFinsetChainField_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitFinsetChainField_last_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {F : Finset (Sym2 (KWDartPort G))}
  {v : V} :
-- imply
  kwOrderedSplitFinsetChainField G order F v (Fin.last (Fintype.card (KWOutgoingDart (G := G) v))) = 0 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitFinsetChainField_last G order F v

/--
[kwExternalPortBits_extract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwExternalPortBits_extract_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 (KWDartPort G))}
  {p : KWDartPort G} :
-- imply
  kwExternalPortBits G (kwOrderedSplitFinsetExternalBits G F) p = if s(p, kwOrderedMatchingNeighbor G p) ∈ F then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.kwExternalPortBits_extract G F p

/--
[kwOrderedSplitFinsetChainField_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitFinsetChainField_castSucc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {F : Finset (Sym2 (KWDartPort G))}
  {v : V}
-- given
  (i : Fin (Fintype.card (KWOutgoingDart (G := G) v)))
  (hpos : 0 < i.val) :
-- imply
  kwOrderedSplitFinsetChainField G order F v i.castSucc = if s(kwPortAtOrderedRank order v ⟨i.val - 1, by omega⟩, kwPortAtOrderedRank order v i) ∈ F then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitFinsetChainField_castSucc G order F v i hpos

/--
[kwOrderedSplitFinsetChainField_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitFinsetChainField_succ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {F : Finset (Sym2 (KWDartPort G))}
  {v : V}
-- given
  (i : Fin (Fintype.card (KWOutgoingDart (G := G) v)))
  (hnext : i.val + 1 < Fintype.card (KWOutgoingDart (G := G) v)) :
-- imply
  kwOrderedSplitFinsetChainField G order F v i.succ = if s(kwPortAtOrderedRank order v i, kwPortAtOrderedRank order v ⟨i.val + 1, hnext⟩) ∈ F then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitFinsetChainField_succ G order F v i hnext

/--
[kw_evenSubgraph_neighbor_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_evenSubgraph_neighbor_sum_zero_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {F : Finset (Sym2 W)}
  {v : W}
-- given
  (hF : F ∈ evenSubgraphs H) :
-- imply
  ∑ w ∈ H.neighborFinset v, (if s(v, w) ∈ F then (1 : ZMod 2) else 0) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_evenSubgraph_neighbor_sum_zero H F hF v

/--
[kwOrderedPortSplitAdjBit_extract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedPortSplitAdjBit_extract_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {F : Finset (Sym2 (KWDartPort G))}
  {p q : KWDartPort G}
-- given
  (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q) :
-- imply
  kwOrderedPortSplitAdjBit G order (kwOrderedSplitFinsetExternalBits G F) (kwOrderedSplitFinsetChainField G order F) p q = if s(p, q) ∈ F then 1 else 0 := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortSplitAdjBit_extract G order F hpq

/--
[kw_fin2_solve_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kw_fin2_solve_recurrence_eq
  {external left right : Fin 2}
-- given
  (h : external + left + right = 0) :
-- imply
  right = left + external := by
-- proof
  apply StatMech.FrontierA.kw_fin2_solve_recurrence external left right h

/--
[kwOrderedSplitFinset_globalEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitFinset_globalEven_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {F : Finset (Sym2 (KWDartPort G))}
-- given
  (hF : F ∈ evenSubgraphs (kwOrderedDartPortSplitGraph G order)) :
-- imply
  KWOrderedGlobalPortChainEven G order (kwOrderedSplitFinsetExternalBits G F) (kwOrderedSplitFinsetChainField G order F) := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitFinset_globalEven G order F hF

/--
[kwOrderedSplitEdges_extract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitEdges_extract_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {F : Finset (Sym2 (KWDartPort G))}
-- given
  (hF : F ∈ evenSubgraphs (kwOrderedDartPortSplitGraph G order)) :
-- imply
  kwOrderedSplitEdges G order (kwOrderedSplitFinsetExternalBits G F) (kwOrderedSplitFinsetChainField G order F) = F := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitEdges_extract G order F hF

/--
[kwOrderedSplitFinsetExternalBits_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitFinsetExternalBits_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G} :
-- imply
  kwOrderedSplitFinsetExternalBits G (kwOrderedSplitEdges G order b y) = b := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitFinsetExternalBits_edges G order b y

/--
[kwOrderedCanonicalPortChainField_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedCanonicalPortChainField_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
-- given
  (hb : KWOriginalPortEven G b) :
-- imply
  KWOrderedGlobalPortChainEven G order b (kwOrderedCanonicalPortChainField G order b) := by
-- proof
  apply StatMech.FrontierA.kwOrderedCanonicalPortChainField_even G order b hb

/--
[kwOrderedPortChainField_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedPortChainField_unique_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y z : KWPortChainField G}
-- given
  (hy : KWOrderedGlobalPortChainEven G order b y)
  (hz : KWOrderedGlobalPortChainEven G order b z) :
-- imply
  y = z := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortChainField_unique G order b y z hy hz

/--
[kwOrderedSplitEdgeProjection_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitEdgeProjection_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : KWDartPort G} :
-- imply
  kwOrderedSplitEdgeProjection s(p, q) = s(p.1, q.1) := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitEdgeProjection_mk p q

/--
[kwOrderedSplit_external_of_projection_not_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplit_external_of_projection_not_diag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p q : KWDartPort G}
-- given
  (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q)
  (hdiag : ¬(kwOrderedSplitEdgeProjection s(p, q)).IsDiag) :
-- imply
  kwDartOfPort G q = (kwDartOfPort G p).symm := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplit_external_of_projection_not_diag G order hpq hdiag

/--
[kwDartOfPort_toProd_of_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwDartOfPort_toProd_of_external_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : KWDartPort G}
-- given
  (hext : kwDartOfPort G q = (kwDartOfPort G p).symm) :
-- imply
  (kwDartOfPort G p).toProd = (p.1, q.1) := by
-- proof
  apply StatMech.FrontierA.kwDartOfPort_toProd_of_external G hext

/--
[kwOrderedSplitEdgeProjection_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitEdgeProjection_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {edge edge' : Sym2 (KWDartPort G)}
-- given
  (hedge : edge ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
  (hedge' : edge' ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
  (hdiag : ¬(kwOrderedSplitEdgeProjection edge).IsDiag)
  (hdiag' : ¬(kwOrderedSplitEdgeProjection edge').IsDiag)
  (heq : kwOrderedSplitEdgeProjection edge = kwOrderedSplitEdgeProjection edge') :
-- imply
  edge = edge' := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitEdgeProjection_injective G order hedge hedge' hdiag hdiag' heq

/--
[kwOrderedSplitWeight_eq_one_of_projection_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitWeight_eq_one_of_projection_diag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {edge : Sym2 (KWDartPort G)}
-- given
  (hdiag : (kwOrderedSplitEdgeProjection edge).IsDiag) :
-- imply
  kwOrderedSplitWeight G weight edge = 1 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitWeight_eq_one_of_projection_diag G weight hdiag

/--
[kwOrderedSplitWeight_eq_projection_of_not_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitWeight_eq_projection_of_not_diag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {weight : Sym2 V → ℂ}
  {edge : Sym2 (KWDartPort G)}
-- given
  (hedge : edge ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
  (hdiag : ¬(kwOrderedSplitEdgeProjection edge).IsDiag) :
-- imply
  kwOrderedSplitWeight G weight edge = weight (kwOrderedSplitEdgeProjection edge) := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitWeight_eq_projection_of_not_diag G order weight hedge hdiag

/--
[kwOrderedSplitEdges_weight_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplitEdges_weight_prod_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {weight : Sym2 V → ℂ}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G} :
-- imply
  (∏ edge ∈ kwOrderedSplitEdges G order b y, kwOrderedSplitWeight G weight edge) = ∏ edge ∈ kwDartEdgeBitsFinset G b, weight edge := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitEdges_weight_prod G order weight b y

/--
[kwEvenPolynomial_eq_sum_actual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwEvenPolynomial_eq_sum_actual_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ} :
-- imply
  kwEvenPolynomial G weight = ∑ F : KWActualEvenSubgraph G, ∏ edge ∈ F.1, weight edge := by
-- proof
  apply StatMech.FrontierA.kwEvenPolynomial_eq_sum_actual G weight

/--
[kwOrderedSplit_evenPolynomial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean)
-/
@[path]
private lemma kwOrderedSplit_evenPolynomial_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {weight : Sym2 V → ℂ} :
-- imply
  kwEvenPolynomial (kwOrderedDartPortSplitGraph G order) (kwOrderedSplitWeight G weight) = kwEvenPolynomial G weight := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplit_evenPolynomial_eq G order weight


-- created on 2026-10-23
