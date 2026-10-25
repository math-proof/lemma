import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part6
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusCellPrimalOfDualEdge_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_of_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (ZMod L × ZMod L)}
-- given
  (he : e ∈ (onsTorusGraph L).edgeFinset) :
-- imply
  torusCellPrimalOfDualEdge L e = ((torusCellCrossing L).symm ⟨e, he⟩ : TorusAmbientEdge L) := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_of_mem L he

/--
[torusCellPrimalOfDualEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (ZMod L × ZMod L)}
-- given
  (he : e ∈ (onsTorusGraph L).edgeFinset) :
-- imply
  torusCellPrimalOfDualEdge L e ∈ (onsTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_mem L he

/--
[torusCellPrimalOfDualEdge_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellPrimalOfDualEdge_injOn_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Set.InjOn (torusCellPrimalOfDualEdge L) (↑(onsTorusGraph L).edgeFinset : Set (Sym2 (ZMod L × ZMod L))) := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimalOfDualEdge_injOn L

/--
[torusCellDualCutGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellDualCutGraph_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {f g : ZMod L × ZMod L} :
-- imply
  (torusCellDualCutGraph L G).Adj f g ↔ (onsTorusGraph L).Adj f g ∧ torusCellPrimalOfDualEdge L s(f, g) ∉ G.edgeSet := by
-- proof
  apply StatMech.BeffaraDC.torusCellDualCutGraph_adj L G f g

/--
[torusCellPrimal_mem_openSub_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellPrimal_mem_openSub_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))}
  {e : Sym2 (ZMod L × ZMod L)}
-- given
  (he : e ∈ (onsTorusGraph L).edgeFinset) :
-- imply
  torusCellPrimalOfDualEdge L e ∈ (FK.openSub (onsTorusGraph L) ω).edgeSet ↔ ω (torusCellPrimalOfDualEdge L e) = true := by
-- proof
  apply StatMech.BeffaraDC.torusCellPrimal_mem_openSub_iff L ω he

/--
[torusCell_openSub_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCell_openSub_dualConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.openSub (onsTorusGraph L) (torusCellDualConfig L ω) = torusCellDualCutGraph L (FK.openSub (onsTorusGraph L) ω) := by
-- proof
  apply StatMech.BeffaraDC.torusCell_openSub_dualConfig L ω

/--
[torusCell_dual_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCell_dual_openCount_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.openCount (onsTorusGraph L) (torusCellDualConfig L ω) = (onsTorusGraph L).edgeFinset.card - FK.openCount (onsTorusGraph L) ω := by
-- proof
  apply StatMech.BeffaraDC.torusCell_dual_openCount L ω

/--
[torusCellDualCutGraph_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellDualCutGraph_bot_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  torusCellDualCutGraph L (⊥ : SimpleGraph (ZMod L × ZMod L)) = onsTorusGraph L := by
-- proof
  apply StatMech.BeffaraDC.torusCellDualCutGraph_bot L

/--
[torusCellDualCutGraph_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellDualCutGraph_full_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  torusCellDualCutGraph L (onsTorusGraph L) = ⊥ := by
-- proof
  apply StatMech.BeffaraDC.torusCellDualCutGraph_full L

/--
[torusCellDualOfPrimalEdge_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellDualOfPrimalEdge_of_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {e : Sym2 (ZMod L × ZMod L)}
-- given
  (he : e ∈ (onsTorusGraph L).edgeFinset) :
-- imply
  torusCellDualOfPrimalEdge L e = (torusCellCrossing L ⟨e, he⟩ : TorusAmbientEdge L) := by
-- proof
  apply StatMech.BeffaraDC.torusCellDualOfPrimalEdge_of_mem L he

/--
[torusCellDualCutGraph_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellDualCutGraph_sup_edge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)}
  {p q : ZMod L × ZMod L}
-- given
  (hpq : (onsTorusGraph L).Adj p q) :
-- imply
  torusCellDualCutGraph L (G ⊔ edge p q) = (torusCellDualCutGraph L G).deleteEdges {torusCellDualOfPrimalEdge L s(p, q)} := by
-- proof
  apply StatMech.BeffaraDC.torusCellDualCutGraph_sup_edge L G hpq

/--
[torusCell_euler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCell_euler_eq
  {L : ℕ}
  [Fact (2 < L)]
  {G : SimpleGraph (ZMod L × ZMod L)} :
-- imply
  (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard + torusCellFaceCount L G = Nat.card G.ConnectedComponent + 1 - torusCellDefect L G := by
-- proof
  apply StatMech.BeffaraDC.torusCell_euler L G

/--
[torusCell_numClusters_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCell_numClusters_dualConfig_eq
  {L : ℕ}
  [Fact (2 < L)]
  {ω : ConfigSpace (Sym2 (ZMod L × ZMod L))} :
-- imply
  FK.numClusters (onsTorusGraph L) (torusCellDualConfig L ω) = torusCellFaceCount L (FK.openSub (onsTorusGraph L) ω) := by
-- proof
  apply StatMech.BeffaraDC.torusCell_numClusters_dualConfig L ω

/--
[torusCellFaceCount_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellFaceCount_bot_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hconn : (onsTorusGraph L).Connected) :
-- imply
  torusCellFaceCount L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 1 := by
-- proof
  apply StatMech.BeffaraDC.torusCellFaceCount_bot L hconn

/--
[torusCellFaceCount_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellFaceCount_full_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  torusCellFaceCount L (onsTorusGraph L) = L ^ 2 := by
-- proof
  apply StatMech.BeffaraDC.torusCellFaceCount_full L

/--
[torusCellDefect_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellDefect_bot_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hconn : (onsTorusGraph L).Connected) :
-- imply
  torusCellDefect L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 0 := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_bot L hconn

/--
[torusCellDefect_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean)
-/
@[path]
private lemma torusCellDefect_full_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hconn : (onsTorusGraph L).Connected) :
-- imply
  torusCellDefect L (onsTorusGraph L) = 2 := by
-- proof
  apply StatMech.BeffaraDC.torusCellDefect_full L hconn


-- created on 2026-10-23
