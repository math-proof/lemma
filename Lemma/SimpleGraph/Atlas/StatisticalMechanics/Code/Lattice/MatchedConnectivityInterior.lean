import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[mci_kingAdj_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingAdj_symm_eq :
-- imply
  Symmetric mci_kingAdj := by
-- proof
  apply StatMech.Lattice.mci_kingAdj_symm

/--
[mci_kingAdj_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingAdj_irrefl_eq :
-- imply
  ∀ u, ¬ mci_kingAdj u u := by
-- proof
  apply StatMech.Lattice.mci_kingAdj_irrefl

/--
[mci_kingGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingGraph_adj_eq
  {u v : Site 2} :
-- imply
  mci_kingGraph.Adj u v ↔ (u 0 - v 0).natAbs ≤ 1 ∧ (u 1 - v 1).natAbs ≤ 1 ∧ u ≠ v := by
-- proof
  apply StatMech.Lattice.mci_kingGraph_adj u v

/--
[mci_hyper_le_king](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_hyper_le_king_eq :
-- imply
  hypercubicLattice 2 ≤ mci_kingGraph := by
-- proof
  apply StatMech.Lattice.mci_hyper_le_king

/--
[mci_kingReachable_of_hyperReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingReachable_of_hyperReachable_eq
  {u v : Site 2}
-- given
  (h : (hypercubicLattice 2).Reachable u v) :
-- imply
  mci_kingGraph.Reachable u v := by
-- proof
  apply StatMech.Lattice.mci_kingReachable_of_hyperReachable h

/--
[mci_kingAdj_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingAdj_diag_eq
  {x y : ℤ}
  {sx sy : ℤ}
-- given
  (hsx : sx = 1 ∨ sx = -1)
  (hsy : sy = 1 ∨ sy = -1) :
-- imply
  mci_kingGraph.Adj (![x, y] : Site 2) ![x + sx, y + sy] := by
-- proof
  apply StatMech.Lattice.mci_kingAdj_diag x y sx sy hsx hsy

/--
[mci_vseg_edge_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_vseg_edge_col_eq
  {col r : ℤ}
  {k : ℕ}
  {u v : Site 2}
-- given
  (he : s(u, v) ∈ (jec_vsegUp col r k).edges) :
-- imply
  u 0 = col ∧ v 0 = col := by
-- proof
  apply StatMech.Lattice.mci_vseg_edge_col col r k he

/--
[mci_hseg_edge_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_hseg_edge_row_eq
  {row t : ℤ}
  {k : ℕ}
  {u v : Site 2}
-- given
  (he : s(u, v) ∈ (jec_hsegRight row t k).edges) :
-- imply
  u 1 = row ∧ v 1 = row := by
-- proof
  apply StatMech.Lattice.mci_hseg_edge_row row t k he

/--
[mci_fjord_no_row1_horizontal_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_fjord_no_row1_horizontal_edge_eq :
-- imply
  s((![3, 1] : Site 2), (![4, 1] : Site 2)) ∉ sdc_fjord.edges := by
-- proof
  apply StatMech.Lattice.mci_fjord_no_row1_horizontal_edge

/--
[mci_fjord_on_31](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_fjord_on_31_eq :
-- imply
  (![3, 1] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.mci_fjord_on_31

/--
[mci_fjord_not_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_fjord_not_fourThin_eq :
-- imply
  ¬ mci_FourThin sdc_fjord := by
-- proof
  apply StatMech.Lattice.mci_fjord_not_fourThin

/--
[mci_fjord_pockets_not_king_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_fjord_pockets_not_king_adjacent_eq :
-- imply
  ¬ mci_kingGraph.Adj (![2, 1] : Site 2) (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.mci_fjord_pockets_not_king_adjacent

/--
[mci_interiorKingGraph_axial_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_interiorKingGraph_axial_adj_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : jil_offSupportInterior Vc}
-- given
  (hadj : (hypercubicLattice 2).Adj (u : Site 2) (v : Site 2)) :
-- imply
  (mci_interiorKingGraph Vc).Adj u v := by
-- proof
  apply StatMech.Lattice.mci_interiorKingGraph_axial_adj Vc hadj

/--
[mci_interiorKingGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_interiorKingGraph_adj_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : jil_offSupportInterior Vc}
-- given
  (hadj : mci_kingGraph.Adj (u : Site 2) (v : Site 2)) :
-- imply
  (mci_interiorKingGraph Vc).Adj u v := by
-- proof
  apply StatMech.Lattice.mci_interiorKingGraph_adj Vc hadj

/--
[mci_interiorStepGraph_le_king](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_interiorStepGraph_le_king_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  jil_interiorStepGraph Vc ≤ mci_interiorKingGraph Vc := by
-- proof
  apply StatMech.Lattice.mci_interiorStepGraph_le_king Vc

/--
[mci_offSupport_neighbor_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_offSupport_neighbor_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z w : Site 2}
-- given
  (hz : z ∈ jil_offSupportInterior Vc)
  (hadj : (hypercubicLattice 2).Adj z w)
  (hwoff : w ∉ Vc.support) :
-- imply
  w ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.mci_offSupport_neighbor_interior Vc hz hadj hwoff

/--
[mci_offSupport_walk_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_offSupport_walk_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ Vc.support)
  (hx : x ∈ jil_offSupportInterior Vc) :
-- imply
  ∀ z ∈ p.support, z ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.mci_offSupport_walk_interior Vc p hp hx

/--
[mci_diagonal_king_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_diagonal_king_bridge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hxy : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hdiag : (![x + 1, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (helb_off : (![x + 1, y] : Site 2) ∉ Vc.support) :
-- imply
  ∃ helb : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc, (mci_interiorKingGraph Vc).Adj ⟨![x, y], hxy⟩ ⟨![x + 1, y], helb⟩ ∧ (mci_interiorKingGraph Vc).Adj ⟨![x + 1, y], helb⟩ ⟨![x + 1, y + 1], hdiag⟩ := by
-- proof
  apply StatMech.Lattice.mci_diagonal_king_bridge Vc hxy hdiag helb_off

/--
[mci_diagonal_king_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_diagonal_king_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hxy : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hdiag : (![x + 1, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (helb_off : (![x + 1, y] : Site 2) ∉ Vc.support) :
-- imply
  (mci_interiorKingGraph Vc).Reachable ⟨![x, y], hxy⟩ ⟨![x + 1, y + 1], hdiag⟩ := by
-- proof
  apply StatMech.Lattice.mci_diagonal_king_reachable Vc hxy hdiag helb_off

/--
[mci_kingStepGraph_walk_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingStepGraph_walk_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : jil_offSupportInterior Vc}
  {w : (mci_interiorKingGraph Vc).Walk x y} :
-- imply
  ∃ p : mci_kingGraph.Walk (x : Site 2) (y : Site 2), ∀ z ∈ p.support, z ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.mci_kingStepGraph_walk_interior Vc w

/--
[mci_kingRowLinked_of_kingStepReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingRowLinked_of_kingStepReachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hstep : ∀ z : jil_offSupportInterior Vc, (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.mci_kingRowLinked_of_kingStepReachable Vc hseedI hstep

/--
[mci_kingRowLinked_of_rowLinked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingRowLinked_of_rowLinked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hlink : jil_RowLinked Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.mci_kingRowLinked_of_rowLinked Vc hlink

/--
[mci_kingInteriorConnected_of_kingStepConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingInteriorConnected_of_kingStepConn_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hstep : ∀ z : jil_offSupportInterior Vc, (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩) :
-- imply
  mci_KingInteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.mci_kingInteriorConnected_of_kingStepConn Vc hseedI hstep

/--
[mci_kingInteriorConnected_of_rowLinked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean)
-/
@[path]
private lemma mci_kingInteriorConnected_of_rowLinked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hlink : jil_RowLinked Vc seed) :
-- imply
  mci_KingInteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.mci_kingInteriorConnected_of_rowLinked Vc hseedI hlink


-- created on 2026-10-23
