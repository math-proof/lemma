import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify.Part6
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexTorusDualCutGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDualCutGraph_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {f g : HexTorusVertex L} :
-- imply
  (triHexTorusDualCutGraph L K).Adj f g ↔ (hexagonalTorusGraph L).Adj f g ∧ triHexTorusPrimalOfDualEdge L s(f, g) ∉ K.edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDualCutGraph_adj L K f g

/--
[triHexTorus_openSub_dualConfig_graphEdgeConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorus_openSub_dualConfig_graphEdgeConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)} :
-- imply
  FK.openSub (hexagonalTorusGraph L) (triHexTorusDualConfig L (graphEdgeConfig K)) = triHexTorusDualCutGraph L K := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_openSub_dualConfig_graphEdgeConfig L K

/--
[triHexTorusFaceCount_eq_dualCutGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusFaceCount_eq_dualCutGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)} :
-- imply
  triHexTorusFaceCount L K = Nat.card (triHexTorusDualCutGraph L K).ConnectedComponent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusFaceCount_eq_dualCutGraph L K

/--
[triHexTorusEdgeStraddles_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusEdgeStraddles_mk_eq
  {S : Set V}
  {x y : V} :
-- imply
  triHexTorusEdgeStraddles S s(x, y) ↔ (x ∈ S ↔ y ∉ S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusEdgeStraddles_mk S x y

/--
[triHexTorusCutDualGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusCutDualGraph_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {S : Set (TorusSite L)}
  {f g : HexTorusVertex L} :
-- imply
  (triHexTorusCutDualGraph L S).Adj f g ↔ (hexagonalTorusGraph L).Adj f g ∧ triHexTorusEdgeStraddles S (triHexTorusPrimalOfDualEdge L s(f, g)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusCutDualGraph_adj L S f g

/--
[triHexTorusPrimalOfDualEdge_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_indexed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a : TriHexTorusEdgeIndex L} :
-- imply
  triHexTorusPrimalOfDualEdge L (hexagonalTorusIndexedEdge L a) = triangularTorusIndexedEdge L ((triHexTorusIndexEquiv L).symm a) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_indexed L a

/--
[triHexTorusPrimalOfDualEdge_index_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_index_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L (hexagonalTorusIndexedEdge L (z, 0)) = s(z, z + (1, 0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_index_zero L z

/--
[triHexTorusPrimalOfDualEdge_index_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_index_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L (hexagonalTorusIndexedEdge L (z, 1)) = s(z, z + (0, 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_index_one L z

/--
[triHexTorusPrimalOfDualEdge_index_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_index_two_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L (hexagonalTorusIndexedEdge L (z, 2)) = s(z + (1, 0), z + (0, 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_index_two L z

/--
[hexagonalTorusGraph_adj_black_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_adj_black_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L}
  {w : HexTorusVertex L} :
-- imply
  (hexagonalTorusGraph L).Adj (z, false) w ↔ ∃ i : Fin 3, w = (z + hexagonalTorusStep L i, true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_adj_black_iff L z w

/--
[hexagonalTorusGraph_adj_white_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_adj_white_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L}
  {w : HexTorusVertex L} :
-- imply
  (hexagonalTorusGraph L).Adj (z, true) w ↔ ∃ i : Fin 3, w = (z - hexagonalTorusStep L i, false) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_adj_white_iff L z w

/--
[hexagonalTorusGraph_neighborFinset_black](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_neighborFinset_black_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  (hexagonalTorusGraph L).neighborFinset (z, false) = {(z + (1, 0), true), (z + (0, 1), true), (z + (1, 1), true)} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_neighborFinset_black L z

/--
[hexagonalTorusGraph_neighborFinset_white](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_neighborFinset_white_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  (hexagonalTorusGraph L).neighborFinset (z, true) = {(z - (1, 0), false), (z - (0, 1), false), (z - (1, 1), false)} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_neighborFinset_white L z

/--
[triHexTorusPrimalOfDualEdge_white_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_white_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L s((z, true), (z - (1, 0), false)) = s(z - (1, 0), z) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_white_zero L z

/--
[triHexTorusPrimalOfDualEdge_white_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_white_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L s((z, true), (z - (0, 1), false)) = s(z - (0, 1), z) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_white_one L z

/--
[triHexTorusPrimalOfDualEdge_white_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_white_two_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L s((z, true), (z - (1, 1), false)) = s(z - (0, 1), z - (1, 0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_white_two L z

/--
[triHexTorusPrimalOfDualEdge_black_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_black_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L s((z, false), (z + (1, 0), true)) = s(z, z + (1, 0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_black_zero L z

/--
[triHexTorusPrimalOfDualEdge_black_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_black_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L s((z, false), (z + (0, 1), true)) = s(z, z + (0, 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_black_one L z

/--
[triHexTorusPrimalOfDualEdge_black_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualEdge_black_two_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  triHexTorusPrimalOfDualEdge L s((z, false), (z + (1, 1), true)) = s(z + (1, 0), z + (0, 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualEdge_black_two L z

/--
[triHexTorusCutDualGraph_degree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusCutDualGraph_degree_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {S : Set (TorusSite L)}
  {v : HexTorusVertex L} :
-- imply
  Even ((triHexTorusCutDualGraph L S).degree v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusCutDualGraph_degree_even L S v

/--
[triHexTorusDualOfPrimalEdge_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDualOfPrimalEdge_of_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (TorusSite L)}
-- given
  (he : e ∈ (triangularTorusGraph L).edgeSet) :
-- imply
  triHexTorusDualOfPrimalEdge L e = (triHexTorusDualEdgeEquiv L ⟨e, he⟩ : (hexagonalTorusGraph L).edgeSet) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDualOfPrimalEdge_of_mem L he

/--
[triHexTorusPrimalOfDualOfPrimalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusPrimalOfDualOfPrimalEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (TorusSite L)}
-- given
  (he : e ∈ (triangularTorusGraph L).edgeSet) :
-- imply
  triHexTorusPrimalOfDualEdge L (triHexTorusDualOfPrimalEdge L e) = e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusPrimalOfDualOfPrimalEdge L he

/--
[triHexTorusDualCutGraph_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDualCutGraph_sup_edge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {p q : TorusSite L}
-- given
  (hpq : (triangularTorusGraph L).Adj p q) :
-- imply
  triHexTorusDualCutGraph L (K ⊔ edge p q) = (triHexTorusDualCutGraph L K).deleteEdges {triHexTorusDualOfPrimalEdge L s(p, q)} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDualCutGraph_sup_edge L K hpq

/--
[triHexTorusCutDualGraph_le_dualCutGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusCutDualGraph_le_dualCutGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {S : Set (TorusSite L)}
-- given
  (hclosed : ∀ {u v}, K.Adj u v → (u ∈ S ↔ v ∈ S)) :
-- imply
  triHexTorusCutDualGraph L S ≤ triHexTorusDualCutGraph L K := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusCutDualGraph_le_dualCutGraph L K S hclosed

/--
[triHexTorusDualCutGraph_crossed_reachable_of_primal_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDualCutGraph_crossed_reachable_of_primal_not_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {p q : TorusSite L}
  {f g : HexTorusVertex L}
-- given
  (hpq : (triangularTorusGraph L).Adj p q)
  (hmerge : ¬ K.Reachable p q)
  (hdual : triHexTorusDualOfPrimalEdge L s(p, q) = s(f, g)) :
-- imply
  ((triHexTorusDualCutGraph L K).deleteEdges {s(f, g)}).Reachable f g := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDualCutGraph_crossed_reachable_of_primal_not_reachable L K hpq hmerge hdual

/--
[triHexTorusFaceCount_sup_edge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusFaceCount_sup_edge_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {p q : TorusSite L}
-- given
  (hpq : (triangularTorusGraph L).Adj p q) :
-- imply
  triHexTorusFaceCount L (K ⊔ edge p q) ≤ triHexTorusFaceCount L K + 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusFaceCount_sup_edge_le L K hpq

/--
[triHexTorusDefect_le_sup_edge_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_le_sup_edge_of_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {p q : TorusSite L}
-- given
  (hpq : (triangularTorusGraph L).Adj p q)
  (hnew : ¬ K.Adj p q)
  (hreach : K.Reachable p q) :
-- imply
  triHexTorusDefect L K ≤ triHexTorusDefect L (K ⊔ edge p q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_le_sup_edge_of_reachable L K hpq hnew hreach

/--
[triHexTorusFaceCount_sup_edge_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusFaceCount_sup_edge_of_not_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {p q : TorusSite L}
-- given
  (hpq : (triangularTorusGraph L).Adj p q)
  (hmerge : ¬ K.Reachable p q) :
-- imply
  triHexTorusFaceCount L (K ⊔ edge p q) = triHexTorusFaceCount L K := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusFaceCount_sup_edge_of_not_reachable L K hpq hmerge

/--
[triHexTorusDefect_sup_edge_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_sup_edge_of_not_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {p q : TorusSite L}
-- given
  (hpq : (triangularTorusGraph L).Adj p q)
  (hmerge : ¬ K.Reachable p q) :
-- imply
  triHexTorusDefect L (K ⊔ edge p q) = triHexTorusDefect L K := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_sup_edge_of_not_reachable L K hpq hmerge

/--
[triHexTorusDefect_le_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_le_sup_edge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
  {p q : TorusSite L}
-- given
  (hpq : (triangularTorusGraph L).Adj p q)
  (hnew : ¬ K.Adj p q) :
-- imply
  triHexTorusDefect L K ≤ triHexTorusDefect L (K ⊔ edge p q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_le_sup_edge L K hpq hnew

/--
[onsTorusGraph_le_triangularTorusGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma onsTorusGraph_le_triangularTorusGraph_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  onsTorusGraph L ≤ triangularTorusGraph L := by
-- proof
  apply StatMech.FK.PeriodicPlanar.onsTorusGraph_le_triangularTorusGraph L

/--
[triangularTorusGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triangularTorusGraph_connected_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  (triangularTorusGraph L).Connected := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusGraph_connected L

/--
[hexagonalTorusGraph_black_reachable_add_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_black_reachable_add_fst_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  (hexagonalTorusGraph L).Reachable (z, false) (z + (1, 0), false) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_black_reachable_add_fst L z

/--
[hexagonalTorusGraph_black_reachable_add_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_black_reachable_add_snd_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L} :
-- imply
  (hexagonalTorusGraph L).Reachable (z, false) (z + (0, 1), false) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_black_reachable_add_snd L z

/--
[hexagonalTorusGraph_black_reachable_of_ons_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_black_reachable_of_ons_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : TorusSite L}
-- given
  (huv : (onsTorusGraph L).Adj u v) :
-- imply
  (hexagonalTorusGraph L).Reachable (u, false) (v, false) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_black_reachable_of_ons_adj L huv

/--
[hexagonalTorusGraph_black_reachable_of_ons_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_black_reachable_of_ons_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : TorusSite L}
-- given
  (huv : (onsTorusGraph L).Reachable u v) :
-- imply
  (hexagonalTorusGraph L).Reachable (u, false) (v, false) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_black_reachable_of_ons_reachable L huv

/--
[hexagonalTorusGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma hexagonalTorusGraph_connected_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  (hexagonalTorusGraph L).Connected := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusGraph_connected L

/--
[triHexTorusDualCutGraph_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDualCutGraph_bot_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  triHexTorusDualCutGraph L (⊥ : SimpleGraph (TorusSite L)) = hexagonalTorusGraph L := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDualCutGraph_bot L

/--
[triHexTorusDualCutGraph_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDualCutGraph_full_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  triHexTorusDualCutGraph L (triangularTorusGraph L) = ⊥ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDualCutGraph_full L

/--
[triangularTorusGraph_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triangularTorusGraph_edge_card_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  (triangularTorusGraph L).edgeFinset.card = 3 * L ^ 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusGraph_edge_card L

/--
[triHexTorusFaceCount_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusFaceCount_bot_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  triHexTorusFaceCount L (⊥ : SimpleGraph (TorusSite L)) = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusFaceCount_bot L

/--
[triHexTorusFaceCount_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusFaceCount_full_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  triHexTorusFaceCount L (triangularTorusGraph L) = 2 * L ^ 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusFaceCount_full L

/--
[triHexTorusDefect_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_bot_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  triHexTorusDefect L (⊥ : SimpleGraph (TorusSite L)) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_bot L

/--
[triHexTorusDefect_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_full_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  triHexTorusDefect L (triangularTorusGraph L) = 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_full L

/--
[triHexTorusDefect_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_nonnegative_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
-- given
  (hK : K ≤ triangularTorusGraph L) :
-- imply
  0 ≤ triHexTorusDefect L K := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_nonnegative L K hK

/--
[triHexTorusDefect_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_le_two_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
-- given
  (hK : K ≤ triangularTorusGraph L) :
-- imply
  triHexTorusDefect L K ≤ 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_le_two L K hK

/--
[triHexTorusDefect_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_classified_eq
  {L : ℕ}
  [Fact (2 < L)]
  {K : SimpleGraph (TorusSite L)}
-- given
  (hK : K ≤ triangularTorusGraph L) :
-- imply
  triHexTorusDefect L K = 0 ∨ triHexTorusDefect L K = 1 ∨ triHexTorusDefect L K = 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_classified L K hK

/--
[triHexTorusDefect_openSub_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean)
-/
@[path]
private lemma triHexTorusDefect_openSub_classified_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (TorusSite L))} :
-- imply
  triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega) = 0 ∨ triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega) = 1 ∨ triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega) = 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefect_openSub_classified L omega


-- created on 2026-10-23
