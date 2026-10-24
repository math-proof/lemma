import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[ons_touchingBondToRectEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_touchingBondToRectEdge_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (ons_touchingBondToRectEdge n) := by
-- proof
  apply StatMech.Onsager.ons_touchingBondToRectEdge_injective n

/--
[ons_plusRectDualCut_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectDualCut_subset_edgeFinset_eq
  {n : Nat}
  {config : AnchoredConfig (ons_PlusWiredVertex 2 n) none} :
-- imply
  ons_plusRectDualCut n config ⊆ (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset := by
-- proof
  apply StatMech.Onsager.ons_plusRectDualCut_subset_edgeFinset n config

/--
[ons_plusDualContourFace_map_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusDualContourFace_map_val_eq
  {n : Nat}
-- given
  (tau : {x // x ∈ box 2 n} -> Bool) :
-- imply
  (ons_plusDualContourFace n tau).image (Sym2.map Subtype.val) = ons_plusDualContour n tau := by
-- proof
  apply StatMech.Onsager.ons_plusDualContourFace_map_val n tau

/--
[ons_plusDualContourFace_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusDualContourFace_isEven_eq
  {n : Nat}
-- given
  (tau : {x // x ∈ box 2 n} -> Bool) :
-- imply
  IsEvenSubgraph (ons_plusDualContourFace n tau) := by
-- proof
  apply StatMech.Onsager.ons_plusDualContourFace_isEven n tau

/--
[ons_plusRectContour_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectContour_isEven_eq
  {n : Nat}
-- given
  (tau : {x // x ∈ box 2 n} -> Bool) :
-- imply
  IsEvenSubgraph (ons_plusRectContour n tau) := by
-- proof
  apply StatMech.Onsager.ons_plusRectContour_isEven n tau

/--
[ons_touchingBondToRectEdge_eq_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_touchingBondToRectEdge_eq_transport_eq
  {n : Nat}
  {edge : ons_PlusWiredBond 2 n} :
-- imply
  ons_touchingBondToRectEdge n edge = Sym2.map (ons_plusDualFaceEquivRect n) (ons_plusDualFaceEdgeLift n (ons_touchingBondEquivPlusDualEdge n edge)) := by
-- proof
  apply StatMech.Onsager.ons_touchingBondToRectEdge_eq_transport n edge

/--
[ons_plusRectDualCut_optionAnchoredEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectDualCut_optionAnchoredEquiv_eq
  {n : Nat}
-- given
  (tau : {x // x ∈ box 2 n} -> Bool) :
-- imply
  ons_plusRectDualCut n (ons_optionAnchoredEquiv tau) = ons_plusRectContour n tau := by
-- proof
  apply StatMech.Onsager.ons_plusRectDualCut_optionAnchoredEquiv n tau

/--
[ons_plusRectDualCut_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectDualCut_isEven_eq
  {n : Nat}
  {config : AnchoredConfig (ons_PlusWiredVertex 2 n) none} :
-- imply
  IsEvenSubgraph (ons_plusRectDualCut n config) := by
-- proof
  apply StatMech.Onsager.ons_plusRectDualCut_isEven n config

/--
[ons_multibondSupportGraph_plusWired_adj_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_multibondSupportGraph_plusWired_adj_some_eq
  {n : Nat}
-- given
  (x y : {z // z ∈ box 2 n})
  (hxy : (StatMech.FK.boxGraph 2 n).Adj x y) :
-- imply
  (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Adj (some x) (some y) := by
-- proof
  apply StatMech.Onsager.ons_multibondSupportGraph_plusWired_adj_some n x y hxy

/--
[ons_plusWiredEastSite_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusWiredEastSite_mem_box_eq
  {n : Nat} :
-- imply
  ons_plusWiredEastSite n ∈ box 2 n := by
-- proof
  apply StatMech.Onsager.ons_plusWiredEastSite_mem_box n

/--
[ons_plusWiredEastOutsideSite_not_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusWiredEastOutsideSite_not_mem_box_eq
  {n : Nat} :
-- imply
  ons_plusWiredEastOutsideSite n ∉ box 2 n := by
-- proof
  apply StatMech.Onsager.ons_plusWiredEastOutsideSite_not_mem_box n

/--
[ons_plusWiredEast_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusWiredEast_adj_eq
  {n : Nat} :
-- imply
  (hypercubicLattice 2).Adj (ons_plusWiredEastSite n) (ons_plusWiredEastOutsideSite n) := by
-- proof
  apply StatMech.Onsager.ons_plusWiredEast_adj n

/--
[ons_multibondSupportGraph_plusWired_root_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_multibondSupportGraph_plusWired_root_adj_eq
  {n : Nat} :
-- imply
  (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Adj none (some ⟨ons_plusWiredEastSite n, ons_plusWiredEastSite_mem_box n⟩) := by
-- proof
  apply StatMech.Onsager.ons_multibondSupportGraph_plusWired_root_adj n

/--
[ons_multibondSupportGraph_plusWired_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_multibondSupportGraph_plusWired_connected_eq
  {n : Nat} :
-- imply
  (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Connected := by
-- proof
  apply StatMech.Onsager.ons_multibondSupportGraph_plusWired_connected n

/--
[ons_plusRectDualCut_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectDualCut_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (ons_plusRectDualCut n) := by
-- proof
  apply StatMech.Onsager.ons_plusRectDualCut_injective n

/--
[ons_rectHorizontalEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectHorizontalEdge_injective_eq
  {M N : Nat} :
-- imply
  Function.Injective (ons_rectHorizontalEdge : ons_RectHorizontalIndex M N -> Sym2 (ons_RectDualVertex M N)) := by
-- proof
  apply StatMech.Onsager.ons_rectHorizontalEdge_injective M N

/--
[ons_rectVerticalEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectVerticalEdge_injective_eq
  {M N : Nat} :
-- imply
  Function.Injective (ons_rectVerticalEdge : ons_RectVerticalIndex M N -> Sym2 (ons_RectDualVertex M N)) := by
-- proof
  apply StatMech.Onsager.ons_rectVerticalEdge_injective M N

/--
[ons_rectHorizontalEdges_disjoint_verticalEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectHorizontalEdges_disjoint_verticalEdges_eq
  {M N : Nat} :
-- imply
  Disjoint (ons_rectHorizontalEdges M N) (ons_rectVerticalEdges M N) := by
-- proof
  apply StatMech.Onsager.ons_rectHorizontalEdges_disjoint_verticalEdges M N

/--
[ons_rectDualGraph_edgeFinset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectDualGraph_edgeFinset_eq_eq
  {M N : Nat} :
-- imply
  (ons_rectDualGraph M N).edgeFinset = ons_rectHorizontalEdges M N ∪ ons_rectVerticalEdges M N := by
-- proof
  apply StatMech.Onsager.ons_rectDualGraph_edgeFinset_eq M N

/--
[ons_rectDualGraph_card_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectDualGraph_card_edgeFinset_eq
  {M N : Nat} :
-- imply
  (ons_rectDualGraph M N).edgeFinset.card = M * (N + 1) + (M + 1) * N := by
-- proof
  apply StatMech.Onsager.ons_rectDualGraph_card_edgeFinset M N

/--
[ons_rectDualGraph_eq_boxProd_pathGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectDualGraph_eq_boxProd_pathGraph_eq
  {M N : Nat} :
-- imply
  ons_rectDualGraph M N = SimpleGraph.pathGraph (M + 1) □ SimpleGraph.pathGraph (N + 1) := by
-- proof
  apply StatMech.Onsager.ons_rectDualGraph_eq_boxProd_pathGraph M N

/--
[ons_rectDualGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectDualGraph_connected_eq
  {M N : Nat} :
-- imply
  (ons_rectDualGraph M N).Connected := by
-- proof
  apply StatMech.Onsager.ons_rectDualGraph_connected M N

/--
[evenSubgraphs_sdiff_tree_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma evenSubgraphs_sdiff_tree_injOn_eq
  [Fintype V]
  [DecidableEq V]
  {G T : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel T.Adj]
-- given
  (hT : T.IsAcyclic) :
-- imply
  Set.InjOn (fun F : Finset (Sym2 V) => F \ T.edgeFinset) (evenSubgraphs G : Set (Finset (Sym2 V))) := by
-- proof
  apply StatMech.Onsager.evenSubgraphs_sdiff_tree_injOn G T hT

/--
[card_evenSubgraphs_le_spanningTree_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma card_evenSubgraphs_le_spanningTree_complement_eq
  [Fintype V]
  [DecidableEq V]
  {G T : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel T.Adj]
-- given
  (hT : T.IsAcyclic) :
-- imply
  (evenSubgraphs G).card ≤ 2 ^ (G.edgeFinset \ T.edgeFinset).card := by
-- proof
  apply StatMech.Onsager.card_evenSubgraphs_le_spanningTree_complement G T hT

/--
[ons_rectDualSpanningTree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectDualSpanningTree_le_eq
  {M N : Nat} :
-- imply
  ons_rectDualSpanningTree M N ≤ ons_rectDualGraph M N := by
-- proof
  apply StatMech.Onsager.ons_rectDualSpanningTree_le M N

/--
[ons_rectDualSpanningTree_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectDualSpanningTree_isTree_eq
  {M N : Nat} :
-- imply
  (ons_rectDualSpanningTree M N).IsTree := by
-- proof
  apply StatMech.Onsager.ons_rectDualSpanningTree_isTree M N

/--
[ons_rectDualSpanningTree_complement_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_rectDualSpanningTree_complement_card_eq
  {n : Nat} :
-- imply
  ((ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset \ (ons_rectDualSpanningTree (2 * n + 1) (2 * n + 1)).edgeFinset).card = (2 * n + 1) ^ 2 := by
-- proof
  apply StatMech.Onsager.ons_rectDualSpanningTree_complement_card n

/--
[ons_plusRectCutEven_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectCutEven_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (ons_plusRectCutEven n) := by
-- proof
  apply StatMech.Onsager.ons_plusRectCutEven_injective n

/--
[card_ons_plusAnchoredConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma card_ons_plusAnchoredConfig_eq
  {n : Nat} :
-- imply
  Fintype.card (AnchoredConfig (ons_PlusWiredVertex 2 n) none) = 2 ^ ((2 * n + 1) ^ 2) := by
-- proof
  apply StatMech.Onsager.card_ons_plusAnchoredConfig n

/--
[card_ons_plusRectEvenSubgraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma card_ons_plusRectEvenSubgraph_le_eq
  {n : Nat} :
-- imply
  Fintype.card (ons_PlusRectEvenSubgraph n) ≤ 2 ^ ((2 * n + 1) ^ 2) := by
-- proof
  apply StatMech.Onsager.card_ons_plusRectEvenSubgraph_le n

/--
[ons_plusRectCutEven_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectCutEven_bijective_eq
  {n : Nat} :
-- imply
  Function.Bijective (ons_plusRectCutEven n) := by
-- proof
  apply StatMech.Onsager.ons_plusRectCutEven_bijective n

/--
[existsUnique_ons_plusRectDualCut_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma existsUnique_ons_plusRectDualCut_eq_eq
  {n : Nat}
  {F : ons_PlusRectEvenSubgraph n} :
-- imply
  ∃! config : AnchoredConfig (ons_PlusWiredVertex 2 n) none, ons_plusRectDualCut n config = F.1 := by
-- proof
  apply StatMech.Onsager.existsUnique_ons_plusRectDualCut_eq n F

/--
[ons_plusRectPathDefectSign_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectPathDefectSign_cut_eq
  {n : Nat}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
  {config : AnchoredConfig (ons_PlusWiredVertex 2 n) none} :
-- imply
  ons_plusRectPathDefectSign n path (ons_plusRectCutEven n config) = (-1 : Real) ^ path.edges.countP (fun primal => decide (primal ∈ (multibondCut (ons_plusWiredBondEnds 2 n) config.1).map ⟨Subtype.val, Subtype.val_injective⟩)) := by
-- proof
  apply StatMech.Onsager.ons_plusRectPathDefectSign_cut n path config

/--
[ons_plusPath_crossCount_eq_wiredCutLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusPath_crossCount_eq_wiredCutLattice_eq
  {n : Nat}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
-- given
  (tau : {x // x ∈ box 2 n} -> Bool) :
-- imply
  kwd_crossCount (kwd_sideBoundary (glue (plusField 2) tau)) path = path.edges.countP (fun edge => decide (edge ∈ ons_plusWiredCutLattice 2 n tau)) := by
-- proof
  apply StatMech.Onsager.ons_plusPath_crossCount_eq_wiredCutLattice n tau path

/--
[ons_plusRectPathDefectSign_optionAnchoredEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectPathDefectSign_optionAnchoredEquiv_eq
  {n : Nat}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v}
-- given
  (tau : {x // x ∈ box 2 n} -> Bool) :
-- imply
  ons_plusRectPathDefectSign n path (ons_plusRectCutEven n (ons_optionAnchoredEquiv tau)) = ons_plusWiredEndpointSign 2 n (ons_optionAnchoredEquiv tau).1 u v := by
-- proof
  apply StatMech.Onsager.ons_plusRectPathDefectSign_optionAnchoredEquiv n tau path

/--
[ons_plusRectPathDefectSign_eq_endpointSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean)
-/
@[path]
private lemma ons_plusRectPathDefectSign_eq_endpointSign_eq
  {n : Nat}
  {F : ons_PlusRectEvenSubgraph n}
  {u v : Site 2}
  {path : (hypercubicLattice 2).Walk u v} :
-- imply
  ons_plusRectPathDefectSign n path F = ons_plusWiredEndpointSign 2 n ((ons_plusRectCutEvenEquiv n).symm F).1 u v := by
-- proof
  apply StatMech.Onsager.ons_plusRectPathDefectSign_eq_endpointSign n F path


-- created on 2026-10-23
