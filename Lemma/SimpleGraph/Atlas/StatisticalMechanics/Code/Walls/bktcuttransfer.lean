import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bktcuttransfer.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bkt_bot_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_bot_reachable_iff_eq
  {d : ℕ}
  {t t' : V} :
-- imply
  (⊥ : SimpleGraph V).Reachable t t' ↔ t = t' := by
-- proof
  apply StatMech.Walls.bkt_bot_reachable_iff t t'

/--
[bkt_ctrGraph_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_ctrGraph_some_some_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d} :
-- imply
  (bkt_ctrGraph ω L y).Adj (some a) (some b) ↔ a ∉ bc61_boxAround d L y ∧ b ∉ bc61_boxAround d L y ∧ (openSubgraph d ω).Adj a b := by
-- proof
  apply StatMech.Walls.bkt_ctrGraph_some_some ω L y a b

/--
[bkt_ctrGraph_none_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_ctrGraph_none_some_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a : Site d} :
-- imply
  (bkt_ctrGraph ω L y).Adj none (some a) ↔ a ∉ bc61_boxAround d L y ∧ bc67_GnIncident ω L y a := by
-- proof
  apply StatMech.Walls.bkt_ctrGraph_none_some ω L y a

/--
[bkt_ctrGraph_none_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_ctrGraph_none_none_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d} :
-- imply
  ¬ (bkt_ctrGraph ω L y).Adj none none := by
-- proof
  apply StatMech.Walls.bkt_ctrGraph_none_none ω L y

/--
[bkt_deleteSuper_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_deleteSuper_adj_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d} :
-- imply
  ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Adj (some a) (some b) ↔ (bc67_contractedLattice ω L y).Adj a b := by
-- proof
  apply StatMech.Walls.bkt_deleteSuper_adj_iff ω L y a b

/--
[bkt_deleteSuper_none_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_deleteSuper_none_isolated_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {v : Option (Site d)} :
-- imply
  ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Adj none v := by
-- proof
  apply StatMech.Walls.bkt_deleteSuper_none_isolated ω L y v

/--
[bkt_deleteSuper_reachable_of_boxCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_deleteSuper_reachable_of_boxCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d}
-- given
  (h : (bc67_contractedLattice ω L y).Reachable a b) :
-- imply
  ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) := by
-- proof
  apply StatMech.Walls.bkt_deleteSuper_reachable_of_boxCut ω L y a b h

/--
[bkt_boxCut_reachable_of_deleteSuper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_boxCut_reachable_of_deleteSuper_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {u v : Option (Site d)}
-- given
  (h : ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable u v) :
-- imply
  ∀ a b : Site d, u = some a → v = some b → (bc67_contractedLattice ω L y).Reachable a b := by
-- proof
  apply StatMech.Walls.bkt_boxCut_reachable_of_deleteSuper ω L y h

/--
[bkt_ctr_deleteSuper_eq_boxCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_ctr_deleteSuper_eq_boxCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d} :
-- imply
  ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) ↔ (bc67_contractedLattice ω L y).Reachable a b := by
-- proof
  apply StatMech.Walls.bkt_ctr_deleteSuper_eq_boxCut ω L y a b

/--
[bkt_perHub_cutTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_perHub_cutTransfer_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d}
-- given
  (hcut : ¬ (bc67_contractedLattice ω L y).Reachable a b) :
-- imply
  ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) := by
-- proof
  apply StatMech.Walls.bkt_perHub_cutTransfer ω L y a b hcut

/--
[bkt_secondBox_not_contracted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_secondBox_not_contracted_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d}
-- given
  (ha : a ∉ bc61_boxAround d L y)
  (hb : b ∉ bc61_boxAround d L y)
  (hopen : (openSubgraph d ω).Adj a b) :
-- imply
  (bkt_ctrGraph ω L y).Adj (some a) (some b) := by
-- proof
  apply StatMech.Walls.bkt_secondBox_not_contracted ω L y a b ha hb hopen

/--
[bkt_box_overconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_box_overconnects_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d}
-- given
  (ha : a ∉ bc61_boxAround d L y)
  (hb : b ∉ bc61_boxAround d L y)
  (hia : bc67_GnIncident ω L y a)
  (hib : bc67_GnIncident ω L y b) :
-- imply
  (bkt_ctrGraph ω L y).Reachable (some a) (some b) := by
-- proof
  apply StatMech.Walls.bkt_box_overconnects ω L y a b ha hb hia hib

/--
[bkt_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d} :
-- imply
  Nonempty (Option (Site d)) ∧ ∀ a b : Site d, (((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) ↔ (bc67_contractedLattice ω L y).Reachable a b) := by
-- proof
  apply StatMech.Walls.bkt_nonvacuous ω L y

/--
[bkt_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean)
-/
@[path]
private lemma bkt_status_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ} :
-- imply
  (∀ (y a b : Site d), ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) ↔ (bc67_contractedLattice ω L y).Reachable a b) ∧ (∀ (y a b : Site d), ¬ (bc67_contractedLattice ω L y).Reachable a b → ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b)) ∧ (∀ (y a b : Site d), a ∉ bc61_boxAround d L y → b ∉ bc61_boxAround d L y → bc67_GnIncident ω L y a → bc67_GnIncident ω L y b → (bkt_ctrGraph ω L y).Reachable (some a) (some b)) := by
-- proof
  apply StatMech.Walls.bkt_status ω L


-- created on 2026-10-23
