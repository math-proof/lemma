import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
open StatMech StatMech.Onsager


/--
[ons_decAdj_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decAdj_symm_eq
  {L : ℕ} :
-- imply
  Symmetric (ons_decAdj L) := by
-- proof
  apply StatMech.Onsager.ons_decAdj_symm L

/--
[ons_dartRev_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_dartRev_ne_self_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  ons_dartRev L d ≠ d := by
-- proof
  apply StatMech.Onsager.ons_dartRev_ne_self L d

/--
[ons_decGraph_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decGraph_neighborFinset_eq
  {L : ℕ}
  [NeZero L]
  {d : ons_Dart L} :
-- imply
  (ons_decGraph L).neighborFinset d = insert (ons_dartRev L d) (ons_decInternalNeighbors d) := by
-- proof
  apply StatMech.Onsager.ons_decGraph_neighborFinset L d

/--
[ons_decGraph_degree_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decGraph_degree_le_three_eq
  {L : ℕ}
  [NeZero L]
  {d : ons_Dart L} :
-- imply
  (ons_decGraph L).degree d ≤ 3 := by
-- proof
  apply StatMech.Onsager.ons_decGraph_degree_le_three L d

/--
[ons_decChainCompletion_even_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decChainCompletion_even_iff_eq
  {b0 b1 b2 b3 : Fin 2} :
-- imply
  ons_decChainEven b0 b1 b2 b3 (ons_decChainCompletion b0 b1 b2) ↔ b0 + b1 + b2 + b3 = 0 := by
-- proof
  apply StatMech.Onsager.ons_decChainCompletion_even_iff b0 b1 b2 b3

/--
[ons_fin2_one_add_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_fin2_one_add_eq_zero_iff_eq
  {x : Fin 2} :
-- imply
  (1 : Fin 2) + x = 0 ↔ x = 1 := by
-- proof
  apply StatMech.Onsager.ons_fin2_one_add_eq_zero_iff x

/--
[ons_decChain_eq_completion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decChain_eq_completion_eq
  {b0 b1 b2 b3 : Fin 2}
  {y : Fin 3 → Fin 2}
-- given
  (heven : b0 + b1 + b2 + b3 = 0)
  (hy : ons_decChainEven b0 b1 b2 b3 y) :
-- imply
  y = ons_decChainCompletion b0 b1 b2 := by
-- proof
  apply StatMech.Onsager.ons_decChain_eq_completion heven hy

/--
[ons_decChain_existsUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decChain_existsUnique_eq
  {b0 b1 b2 b3 : Fin 2}
-- given
  (heven : b0 + b1 + b2 + b3 = 0) :
-- imply
  ∃! y : Fin 3 → Fin 2, ons_decChainEven b0 b1 b2 b3 y := by
-- proof
  apply StatMech.Onsager.ons_decChain_existsUnique b0 b1 b2 b3 heven

/--
[ons_decChainEven_port_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decChainEven_port_even_eq
  {b0 b1 b2 b3 : Fin 2}
  {y : Fin 3 → Fin 2}
-- given
  (hy : ons_decChainEven b0 b1 b2 b3 y) :
-- imply
  b0 + b1 + b2 + b3 = 0 := by
-- proof
  apply StatMech.Onsager.ons_decChainEven_port_even hy

/--
[ons_PortPattern.ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ext_eq
  {L : ℕ}
  {P Q : ons_PortPattern L}
-- given
  (h : P.bit = Q.bit) :
-- imply
  P = Q := by
-- proof
  apply StatMech.Onsager.ons_PortPattern.ext h

/--
[ons_decNeighborBit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decNeighborBit_symm_eq
  {L : ℕ}
  {P : ons_PortPattern L}
  {d e : ons_Dart L} :
-- imply
  ons_decNeighborBit P d e = ons_decNeighborBit P e d := by
-- proof
  apply StatMech.Onsager.ons_decNeighborBit_symm P d e

/--
[ons_decEdgeBit_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decEdgeBit_mk_eq
  {L : ℕ}
  {P : ons_PortPattern L}
  {d e : ons_Dart L} :
-- imply
  ons_decEdgeBit P s(d, e) = ons_decNeighborBit P d e := by
-- proof
  apply StatMech.Onsager.ons_decEdgeBit_mk P d e

/--
[ons_incidenceFinset_eq_image_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_incidenceFinset_eq_image_neighborFinset_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {v : V} :
-- imply
  H.incidenceFinset v = (H.neighborFinset v).image (fun w => s(v, w)) := by
-- proof
  apply StatMech.Onsager.ons_incidenceFinset_eq_image_neighborFinset H v

/--
[ons_neighborEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_neighborEdge_injective_eq
  [DecidableEq V]
  {H : SimpleGraph V}
  {v : V} :
-- imply
  Set.InjOn (fun w => s(v, w)) (H.neighborSet v) := by
-- proof
  apply StatMech.Onsager.ons_neighborEdge_injective H v

/--
[ons_incCount_filter_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_incCount_filter_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidablePred Q]
  {v : V}
-- given
  (Q : Sym2 V → Prop) :
-- imply
  incCount (H.edgeFinset.filter Q) v = ((H.incidenceFinset v).filter Q).card := by
-- proof
  apply StatMech.Onsager.ons_incCount_filter_edgeFinset H Q v

/--
[ons_cast_incCount_filter_eq_neighbor_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_cast_incCount_filter_eq_neighbor_sum_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidablePred Q]
  {v : V}
-- given
  (Q : Sym2 V → Prop) :
-- imply
  ((incCount (H.edgeFinset.filter Q) v : ℕ) : ZMod 2) = ∑ w ∈ H.neighborFinset v, if Q s(v, w) then (1 : ZMod 2) else 0 := by
-- proof
  apply StatMech.Onsager.ons_cast_incCount_filter_eq_neighbor_sum H Q v

/--
[ons_evenSubgraph_neighbor_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_evenSubgraph_neighbor_sum_zero_eq
  [Fintype V]
  [DecidableEq V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {F : Finset (Sym2 V)}
  {v : V}
-- given
  (hF : F ∈ evenSubgraphs H) :
-- imply
  ∑ w ∈ H.neighborFinset v, (if s(v, w) ∈ F then (1 : ZMod 2) else 0) = 0 := by
-- proof
  apply StatMech.Onsager.ons_evenSubgraph_neighbor_sum_zero H F hF v

/--
[ons_fin2_indicator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_fin2_indicator_eq_eq
  {a : Fin 2} :
-- imply
  (if a = 1 then (1 : Fin 2) else 0) = a := by
-- proof
  apply StatMech.Onsager.ons_fin2_indicator_eq a

/--
[ons_dirStep_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_dirStep_ne_self_eq
  {L : ℕ}
  [Fact (2 < L)]
  {mu : Fin 4}
  {s : ZMod L × ZMod L} :
-- imply
  ons_dirStep L mu s ≠ s := by
-- proof
  apply StatMech.Onsager.ons_dirStep_ne_self L mu s

/--
[ons_decInternalNeighbors_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decInternalNeighbors_site_eq
  {L : ℕ}
  {d e : ons_Dart L}
-- given
  (he : e ∈ ons_decInternalNeighbors d) :
-- imply
  e.1 = d.1 := by
-- proof
  apply StatMech.Onsager.ons_decInternalNeighbors_site he

/--
[ons_dartRev_not_mem_internalNeighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_dartRev_not_mem_internalNeighbors_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  ons_dartRev L d ∉ ons_decInternalNeighbors d := by
-- proof
  apply StatMech.Onsager.ons_dartRev_not_mem_internalNeighbors L d

/--
[ons_decNeighborBit_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decNeighborBit_sum_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : ons_PortPattern L}
  {d : ons_Dart L} :
-- imply
  ∑ e ∈ (ons_decGraph L).neighborFinset d, ons_decNeighborBit P d e = 0 := by
-- proof
  apply StatMech.Onsager.ons_decNeighborBit_sum_zero L P d

/--
[ons_portEdge_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_portEdge_rev_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  ons_portEdge L (ons_dartRev L d) = ons_portEdge L d := by
-- proof
  apply StatMech.Onsager.ons_portEdge_rev L d

/--
[ons_torus_neighborFinset_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_torus_neighborFinset_steps_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ZMod L × ZMod L} :
-- imply
  (onsTorusGraph L).neighborFinset v = {ons_dirStep L 0 v, ons_dirStep L 1 v, ons_dirStep L 2 v, ons_dirStep L 3 v} := by
-- proof
  apply StatMech.Onsager.ons_torus_neighborFinset_steps L v

/--
[ons_dirStep_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_dirStep_injective_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ZMod L × ZMod L} :
-- imply
  Function.Injective (fun mu : Fin 4 => ons_dirStep L mu v) := by
-- proof
  apply StatMech.Onsager.ons_dirStep_injective L v

/--
[ons_torus_neighbor_sum_eq_direction_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_torus_neighbor_sum_eq_direction_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ZMod L × ZMod L}
  {f : (ZMod L × ZMod L) → ZMod 2} :
-- imply
  ∑ w ∈ (onsTorusGraph L).neighborFinset v, f w = ∑ mu : Fin 4, f (ons_dirStep L mu v) := by
-- proof
  apply StatMech.Onsager.ons_torus_neighbor_sum_eq_direction_sum L v f

/--
[ons_decorated_local_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decorated_local_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : Finset (Sym2 (ons_Dart L))}
  {s : ZMod L × ZMod L}
-- given
  (hD : D ∈ evenSubgraphs (ons_decGraph L)) :
-- imply
  ons_decChainEven (ons_decoratedPortBit D (s, 0)) (ons_decoratedPortBit D (s, 1)) (ons_decoratedPortBit D (s, 2)) (ons_decoratedPortBit D (s, 3)) (ons_decoratedChainBits D s) := by
-- proof
  apply StatMech.Onsager.ons_decorated_local_even L D hD s

/--
[ons_decoratedChainBits_eq_completion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decoratedChainBits_eq_completion_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : Finset (Sym2 (ons_Dart L))}
  {s : ZMod L × ZMod L}
-- given
  (hD : D ∈ evenSubgraphs (ons_decGraph L)) :
-- imply
  ons_decoratedChainBits D s = ons_portChainBit (ons_portPatternOfDecorated L D hD) s := by
-- proof
  apply StatMech.Onsager.ons_decoratedChainBits_eq_completion L D hD s

/--
[ons_decoratedEdges_portPatternOfDecorated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decoratedEdges_portPatternOfDecorated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : Finset (Sym2 (ons_Dart L))}
-- given
  (hD : D ∈ evenSubgraphs (ons_decGraph L)) :
-- imply
  ons_decoratedEdges (ons_portPatternOfDecorated L D hD) = D := by
-- proof
  apply StatMech.Onsager.ons_decoratedEdges_portPatternOfDecorated L D hD

/--
[ons_decEdgeBit_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decEdgeBit_external_eq
  {L : ℕ}
  {P : ons_PortPattern L}
  {d : ons_Dart L} :
-- imply
  ons_decEdgeBit P s(d, ons_dartRev L d) = P.bit d := by
-- proof
  apply StatMech.Onsager.ons_decEdgeBit_external P d

/--
[ons_decorated_external_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decorated_external_mem_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {d : ons_Dart L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  s(d, ons_dartRev L d) ∈ ons_decoratedEdges (ons_evenSubgraphPortPattern L F hF) ↔ ons_portEdge L d ∈ F := by
-- proof
  apply StatMech.Onsager.ons_decorated_external_mem_iff L F hF d

/--
[ons_decoratedEdges_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decoratedEdges_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : ons_PortPattern L} :
-- imply
  ons_decoratedEdges P ∈ evenSubgraphs (ons_decGraph L) := by
-- proof
  apply StatMech.Onsager.ons_decoratedEdges_even L P

/--
[ons_portEdge_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_portEdge_mem_edgeFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  ons_portEdge L d ∈ (onsTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.Onsager.ons_portEdge_mem_edgeFinset L d

/--
[ons_portEdge_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_portEdge_eq_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L} :
-- imply
  ons_portEdge L e = ons_portEdge L d ↔ e = d ∨ e = ons_dartRev L d := by
-- proof
  apply StatMech.Onsager.ons_portEdge_eq_iff L d e

/--
[ons_portEdge_mem_portPatternEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_portEdge_mem_portPatternEdges_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : ons_PortPattern L}
  {d : ons_Dart L} :
-- imply
  ons_portEdge L d ∈ ons_portPatternEdges L P ↔ P.bit d = 1 := by
-- proof
  apply StatMech.Onsager.ons_portEdge_mem_portPatternEdges_iff L P d

/--
[ons_torusEdge_eq_portEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_torusEdge_eq_portEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {edge : Sym2 (ZMod L × ZMod L)}
-- given
  (hedge : edge ∈ (onsTorusGraph L).edgeFinset) :
-- imply
  ∃ d : ons_Dart L, ons_portEdge L d = edge := by
-- proof
  apply StatMech.Onsager.ons_torusEdge_eq_portEdge L hedge

/--
[ons_portPatternEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_portPatternEdges_subset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : ons_PortPattern L} :
-- imply
  ons_portPatternEdges L P ⊆ (onsTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.Onsager.ons_portPatternEdges_subset L P

/--
[ons_portPatternEdges_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_portPatternEdges_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : ons_PortPattern L} :
-- imply
  ons_portPatternEdges L P ∈ evenSubgraphs (onsTorusGraph L) := by
-- proof
  apply StatMech.Onsager.ons_portPatternEdges_even L P

/--
[ons_portPatternEdges_evenSubgraphPortPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_portPatternEdges_evenSubgraphPortPattern_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_portPatternEdges L (ons_evenSubgraphPortPattern L F hF) = F := by
-- proof
  apply StatMech.Onsager.ons_portPatternEdges_evenSubgraphPortPattern L F hF

/--
[ons_evenSubgraphPortPattern_portPatternEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_evenSubgraphPortPattern_portPatternEdges_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : ons_PortPattern L} :
-- imply
  ons_evenSubgraphPortPattern L (ons_portPatternEdges L P) (ons_portPatternEdges_even L P) = P := by
-- proof
  apply StatMech.Onsager.ons_evenSubgraphPortPattern_portPatternEdges L P

/--
[ons_portPatternOfDecorated_decoratedEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_portPatternOfDecorated_decoratedEdges_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : ons_PortPattern L} :
-- imply
  ons_portPatternOfDecorated L (ons_decoratedEdges P) (ons_decoratedEdges_even L P) = P := by
-- proof
  apply StatMech.Onsager.ons_portPatternOfDecorated_decoratedEdges L P

/--
[ons_decorated_evenSubgraph_cycle_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean)
-/
@[path]
private lemma ons_decorated_evenSubgraph_cycle_decomposition_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  let D := ons_decoratedEdges (ons_evenSubgraphPortPattern L F hF) ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (base : ι → ons_Dart L) (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)), (∀ i, (p i).IsCycle) ∧ D = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).edges.toFinset) := by
-- proof
  apply StatMech.Onsager.ons_decorated_evenSubgraph_cycle_decomposition L F hF


-- created on 2026-10-23
