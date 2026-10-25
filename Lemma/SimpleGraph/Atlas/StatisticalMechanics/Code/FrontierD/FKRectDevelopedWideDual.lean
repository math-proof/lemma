import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual.Part5
open Set StatMech StatMech.FrontierD


/--
[fkRectWideExteriorOpenExtension_eq_swap_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWideExteriorOpenExtension_eq_swap_of_mem_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ StatMech.Percolation.edgesWithinFinset (fkRectWideTallFinset n)) :
-- imply
  fkRectWideExteriorOpenExtension n eta e = StatMech.Universality.crf_swapConfig eta e := by
-- proof
  apply StatMech.FrontierD.fkRectWideExteriorOpenExtension_eq_swap_of_mem n eta he

/--
[fkRectWideExteriorOpenExtension_not_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWideExteriorOpenExtension_not_horizontal_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
-- imply
  ¬ HorizontalCrossing (fkRectWideExteriorOpenExtension n eta) 0 (3 * n) 0 (3 * n) := by
-- proof
  apply StatMech.FrontierD.fkRectWideExteriorOpenExtension_not_horizontal n hn eta hno

/--
[fkRectWide_faceDualExtension_sharedPrimalEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_faceDualExtension_sharedPrimalEdge_mem_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2}
-- given
  (hfg : (openSubgraph 2 (StatMech.Universality.fci_faceDualConfig (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
-- imply
  sharedPrimalEdge f g ∈ StatMech.Percolation.edgesWithinFinset (fkRectWideTallFinset n) := by
-- proof
  apply StatMech.FrontierD.fkRectWide_faceDualExtension_sharedPrimalEdge_mem n eta hfg

/--
[fkRectWide_endpoint_mem_tall_of_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_endpoint_mem_tall_of_edge_mem_eq
  {n : Int}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ StatMech.Percolation.edgesWithinFinset (fkRectWideTallFinset n))
  (hz : z ∈ e) :
-- imply
  z ∈ fkRectWideTallFinset n := by
-- proof
  apply StatMech.FrontierD.fkRectWide_endpoint_mem_tall_of_edge_mem n he hz

/--
[fkRectWide_faceDualExtension_adj_fst_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_faceDualExtension_adj_fst_le_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2}
-- given
  (hfg : (openSubgraph 2 (StatMech.Universality.fci_faceDualConfig (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
-- imply
  f 0 ≤ n ∧ g 0 ≤ n := by
-- proof
  apply StatMech.FrontierD.fkRectWide_faceDualExtension_adj_fst_le n eta hfg

/--
[fkRectWide_faceDualExtension_vertical_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_faceDualExtension_vertical_band_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
-- imply
  VerticalCrossing (StatMech.Universality.fci_faceDualConfig (fkRectWideExteriorOpenExtension n eta)) 0 (3 * n - 1) (-1) (3 * n) := by
-- proof
  apply StatMech.FrontierD.fkRectWide_faceDualExtension_vertical_band n hn eta hno

/--
[fkRectWide_faceDualExtension_vertical_confined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_faceDualExtension_vertical_confined_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
-- imply
  VerticalCrossing (StatMech.Universality.fci_faceDualConfig (fkRectWideExteriorOpenExtension n eta)) 0 n (-1) (3 * n) := by
-- proof
  apply StatMech.FrontierD.fkRectWide_faceDualExtension_vertical_confined n hn eta hno

/--
[fkRectWide_faceDualExtension_adj_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_faceDualExtension_adj_swap_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2}
-- given
  (hfg : (openSubgraph 2 (StatMech.Universality.fci_faceDualConfig (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
-- imply
  (openSubgraph 2 (StatMech.Universality.fci_faceDualConfig eta)).Adj (StatMech.Universality.crf_swap f) (StatMech.Universality.crf_swap g) := by
-- proof
  apply StatMech.FrontierD.fkRectWide_faceDualExtension_adj_swap n eta hfg

/--
[fkRectWide_faceDualExtension_horizontal_expanded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_faceDualExtension_horizontal_expanded_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
-- imply
  HorizontalCrossing (StatMech.Universality.fci_faceDualConfig eta) (-1) (3 * n) 0 n := by
-- proof
  apply StatMech.FrontierD.fkRectWide_faceDualExtension_horizontal_expanded n hn eta hno

/--
[fkRectWide_faceBand_horizontalCrossing_to_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_faceBand_horizontalCrossing_to_rect_eq
  {eta : ConfigSpace (Sym2 (Site 2))}
  {W H : Int}
-- given
  (hW : 0 < W)
  (h : HorizontalCrossing eta (-1) W 0 H) :
-- imply
  HorizontalCrossing eta 0 W 0 H := by
-- proof
  apply StatMech.FrontierD.fkRectWide_faceBand_horizontalCrossing_to_rect hW h

/--
[fkRectWide_faceDualHorizontal_of_not_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectWide_faceDualHorizontal_of_not_vertical_eq
  {n : Int}
  {eta : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
-- imply
  HorizontalCrossing (StatMech.Universality.fci_faceDualConfig eta) 0 (3 * n) 0 n := by
-- proof
  apply StatMech.FrontierD.fkRectWide_faceDualHorizontal_of_not_vertical n hn eta hno

/--
[fkRectDevelopedThreeByOneVertex_fst_succ_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneVertex_fst_succ_lt_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
-- imply
  (fkRectDevelopedSquareVertex R n z).1.val + 1 < R.width := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneVertex_fst_succ_lt R n hn hwidth hheight hz

/--
[fkRectDualEdgeToEdge_not_cut_of_developedThreeByOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDualEdgeToEdge_not_cut_of_developedThreeByOne_eq
  {R : FKRectTorus}
  {n : Nat}
  {f g : Site 2}
  {d : R.EdgeIndex}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hf : f ∈ fkRectDevelopedThreeByOneRect n)
  (hg : g ∈ fkRectDevelopedThreeByOneRect n)
  (hedge : fkRectTorusIndexedEdge R d = s(fkRectDevelopedSquareVertex R n f, fkRectDevelopedSquareVertex R n g))
  (hd : d ∉ fkRectTorusCutEdges R) :
-- imply
  fkRectDualEdgeToEdge R d ∉ fkRectTorusCutEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectDualEdgeToEdge_not_cut_of_developedThreeByOne R n hn hwidth hheight hf hg d hedge hd

/--
[fkRectDevelopedThreeByOne_faceDual_adj_imp_dual_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_faceDual_adj_imp_dual_adj_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
  {f g : Site 2}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hf : f ∈ fkRectDevelopedThreeByOneRect n)
  (hg : g ∈ fkRectDevelopedThreeByOneRect n)
  (hfg : (openSubgraph 2 (StatMech.Universality.fci_faceDualConfig (fkRectDevelopedSquarePullback R n omega))).Adj f g) :
-- imply
  (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Adj (fkRectDevelopedSquareVertex R n f) (fkRectDevelopedSquareVertex R n g) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_faceDual_adj_imp_dual_adj R n hn hwidth hheight omega hf hg hfg

/--
[fkRectDevelopedThreeByOne_faceDual_connectedWithin_imp_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_faceDual_connectedWithin_imp_dual_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
  {x y : fkRectDevelopedThreeByOneRect n}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hxy : ConnectedWithin 2 (StatMech.Universality.fci_faceDualConfig (fkRectDevelopedSquarePullback R n omega)) (fkRectDevelopedThreeByOneRect n) x y) :
-- imply
  ConnectedWithin 2 (fkRectDevelopedSquarePullback R n (fkRectDualConfigurationEquiv R omega)) (fkRectDevelopedThreeByOneRect n) x y := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_faceDual_connectedWithin_imp_dual R n hn hwidth hheight omega hxy

/--
[fkRectDevelopedThreeByOne_faceDualHorizontal_imp_dualHorizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_faceDualHorizontal_imp_dualHorizontal_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hcross : omega ∈ fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
-- imply
  fkRectDualConfigurationEquiv R omega ∈ fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_faceDualHorizontal_imp_dualHorizontal R n hn hwidth hheight omega hcross

/--
[fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆ fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_compl_subset_faceDualHorizontal R n hn

/--
[fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hface : (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆ fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
-- imply
  fkRectDualEvent R (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆ fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_of_faceDual R n hn hwidth hheight hface

/--
[fkRectDevelopedThreeByOne_dualCompl_subset_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_dualCompl_subset_horizontal_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height) :
-- imply
  fkRectDualEvent R (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆ fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_dualCompl_subset_horizontal R n hn hwidth hheight

/--
[fkRectDevelopedThreeByOne_dualPreimageHorizontalCompl_subset_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_dualPreimageHorizontalCompl_subset_vertical_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height) :
-- imply
  fkRectDualPreimageEvent R (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆ fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_dualPreimageHorizontalCompl_subset_vertical R n hn hwidth hheight

/--
[fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal_of_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal_of_faceDual_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q)
  (hface : (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n)ᶜ ⊆ fkRectDevelopedThreeByOneFaceDualHorizontalEvent R n) :
-- imply
  1 ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n) + q ^ 2 * fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal_of_faceDual R n hn hwidth hheight hq hface

/--
[fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  1 ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n) + q ^ 2 * fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal R n hn hwidth hheight hq

/--
[fkRectCritical_one_le_threeByOneHorizontal_add_q_sq_mul_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean)
-/
@[path]
private lemma fkRectCritical_one_le_threeByOneHorizontal_add_q_sq_mul_vertical_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  1 ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n) + q ^ 2 * fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_one_le_threeByOneHorizontal_add_q_sq_mul_vertical R n hn hwidth hheight hq


-- created on 2026-10-23
