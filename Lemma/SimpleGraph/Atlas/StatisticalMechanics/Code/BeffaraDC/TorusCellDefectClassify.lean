import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify.Part3
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusCellEdgeStraddles_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellEdgeStraddles_mk_eq
  {S : Set V}
  {x y : V} :
-- imply
  torusCellEdgeStraddles S s(x, y) ↔ (x ∈ S ↔ y ∉ S) := by
-- proof
  apply StatMech.BeffaraDC.torusCellEdgeStraddles_mk S x y

/--
[torusCellCutDualGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellCutDualGraph_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {S : Set (ZMod L × ZMod L)}
  {f g : ZMod L × ZMod L} :
-- imply
  (torusCellCutDualGraph L S).Adj f g ↔ (onsTorusGraph L).Adj f g ∧ torusCellEdgeStraddles S (torusCellPrimalOfDualEdge L s(f, g)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCutDualGraph_adj L S f g

/--
[torusCellPrimalOfDualEdge_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_horizontal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  torusCellPrimalOfDualEdge L s((x, y), (x + 1, y)) = s((x + 1, y), (x + 1, y + 1)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_horizontal L x y

/--
[torusCellPrimalOfDualEdge_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_vertical_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  torusCellPrimalOfDualEdge L s((x, y), (x, y + 1)) = s((x, y + 1), (x + 1, y + 1)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_vertical L x y

/--
[torusCellPrimalOfDualEdge_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_down_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  torusCellPrimalOfDualEdge L s((x, y), (x, y - 1)) = s((x, y), (x + 1, y)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_down L x y

/--
[torusCellPrimalOfDualEdge_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_left_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  torusCellPrimalOfDualEdge L s((x, y), (x - 1, y)) = s((x, y), (x, y + 1)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_left L x y

/--
[torusCellPrimalOfDualEdge_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_up_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  torusCellPrimalOfDualEdge L s((x, y), (x, y + 1)) = s((x, y + 1), (x + 1, y + 1)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_up L x y

/--
[torusCellPrimalOfDualEdge_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_right_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  torusCellPrimalOfDualEdge L s((x, y), (x + 1, y)) = s((x + 1, y), (x + 1, y + 1)) := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_right L x y

/--
[torusCell_ambient_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCell_ambient_neighborFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ZMod L × ZMod L} :
-- imply
  (onsTorusGraph L).neighborFinset v = {(v.1, v.2 - 1), (v.1, v.2 + 1), (v.1 - 1, v.2), (v.1 + 1, v.2)} := by
-- proof
  apply StatMech.BeffaraDC.torusCell_ambient_neighborFinset L v

/--
[torusCellCutDualGraph_degree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellCutDualGraph_degree_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {S : Set (ZMod L × ZMod L)}
  {v : ZMod L × ZMod L} :
-- imply
  Even ((torusCellCutDualGraph L S).degree v) := by
-- proof
  apply StatMech.BeffaraDC.torusCellCutDualGraph_degree_even L S v

/--
[torusCellPrimalOfDualOfPrimalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellPrimalOfDualOfPrimalEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (ZMod L × ZMod L)}
-- given
  (he : e ∈ (onsTorusGraph L).edgeFinset) :
-- imply
  torusCellPrimalOfDualEdge L (torusCellDualOfPrimalEdge L e) = e := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualOfPrimalEdge L he

/--
[torusCellCutDualGraph_le_dualCutGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellCutDualGraph_le_dualCutGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {S : Set (ZMod L × ZMod L)}
-- given
  (hclosed : ∀ {u v}, G.Adj u v → (u ∈ S ↔ v ∈ S)) :
-- imply
  torusCellCutDualGraph L S ≤ torusCellDualCutGraph L G := by
-- proof
  apply StatMech.BeffaraDC.torusCellCutDualGraph_le_dualCutGraph L G S hclosed

/--
[torusCellDualCutGraph_crossed_reachable_of_primal_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDualCutGraph_crossed_reachable_of_primal_not_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {p q f g : ZMod L × ZMod L}
-- given
  (hpq : (onsTorusGraph L).Adj p q)
  (hmerge : ¬ G.Reachable p q)
  (hdual : torusCellDualOfPrimalEdge L s(p, q) = s(f, g)) :
-- imply
  ((torusCellDualCutGraph L G).deleteEdges {s(f, g)}).Reachable f g := by
-- proof
  apply StatMech.BeffaraDC.torusCellDualCutGraph_crossed_reachable_of_primal_not_reachable L G hpq hmerge hdual

/--
[torusCellFaceCount_sup_edge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellFaceCount_sup_edge_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {p q : ZMod L × ZMod L}
-- given
  (hpq : (onsTorusGraph L).Adj p q) :
-- imply
  torusCellFaceCount L (G ⊔ edge p q) ≤ torusCellFaceCount L G + 1 := by
-- proof
  apply StatMech.BeffaraDC.torusCellFaceCount_sup_edge_le L G hpq

/--
[torusCellDefect_le_sup_edge_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_le_sup_edge_of_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {p q : ZMod L × ZMod L}
-- given
  (hpq : (onsTorusGraph L).Adj p q)
  (hnew : ¬ G.Adj p q)
  (hreach : G.Reachable p q) :
-- imply
  torusCellDefect L G ≤ torusCellDefect L (G ⊔ edge p q) := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_le_sup_edge_of_reachable L G hpq hnew hreach

/--
[torusCellFaceCount_sup_edge_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellFaceCount_sup_edge_of_not_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {p q : ZMod L × ZMod L}
-- given
  (hpq : (onsTorusGraph L).Adj p q)
  (hmerge : ¬ G.Reachable p q) :
-- imply
  torusCellFaceCount L (G ⊔ edge p q) = torusCellFaceCount L G := by
-- proof
  apply StatMech.BeffaraDC.torusCellFaceCount_sup_edge_of_not_reachable L G hpq hmerge

/--
[torusCellDefect_sup_edge_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_sup_edge_of_not_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {p q : ZMod L × ZMod L}
-- given
  (hpq : (onsTorusGraph L).Adj p q)
  (hmerge : ¬ G.Reachable p q) :
-- imply
  torusCellDefect L (G ⊔ edge p q) = torusCellDefect L G := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_sup_edge_of_not_reachable L G hpq hmerge

/--
[torusCellDefect_le_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_le_sup_edge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {p q : ZMod L × ZMod L}
-- given
  (hpq : (onsTorusGraph L).Adj p q)
  (hnew : ¬ G.Adj p q) :
-- imply
  torusCellDefect L G ≤ torusCellDefect L (G ⊔ edge p q) := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_le_sup_edge L G hpq hnew

/--
[torusCellDefect_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_nonnegative_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hconn : (onsTorusGraph L).Connected)
  (hG : G ≤ onsTorusGraph L) :
-- imply
  0 ≤ torusCellDefect L G := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_nonnegative L G hconn hG

/--
[torusCellDefect_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_le_two_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hconn : (onsTorusGraph L).Connected)
  (hG : G ≤ onsTorusGraph L) :
-- imply
  torusCellDefect L G ≤ 2 := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_le_two L G hconn hG

/--
[torusCellDefect_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_classified_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hconn : (onsTorusGraph L).Connected)
  (hG : G ≤ onsTorusGraph L) :
-- imply
  torusCellDefect L G = 0 ∨ torusCellDefect L G = 1 ∨ torusCellDefect L G = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_classified L G hconn hG

/--
[torusCellDefect_nonnegative_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_nonnegative_unconditional_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hG : G ≤ onsTorusGraph L) :
-- imply
  0 ≤ torusCellDefect L G := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_nonnegative_unconditional L G hG

/--
[torusCellDefect_le_two_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_le_two_unconditional_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hG : G ≤ onsTorusGraph L) :
-- imply
  torusCellDefect L G ≤ 2 := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_le_two_unconditional L G hG

/--
[torusCellDefect_classified_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDefectClassify.lean)
-/
@[path]
private lemma torusCellDefect_classified_unconditional_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
-- given
  (hG : G ≤ onsTorusGraph L) :
-- imply
  torusCellDefect L G = 0 ∨ torusCellDefect L G = 1 ∨ torusCellDefect L G = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_classified_unconditional L G hG


-- created on 2026-10-23
