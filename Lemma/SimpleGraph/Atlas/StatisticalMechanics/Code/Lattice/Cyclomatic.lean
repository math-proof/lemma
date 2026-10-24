import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.Cyclomatic
open StatMech StatMech.Lattice


/--
[tree_card_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma tree_card_edges_eq
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.IsTree) :
-- imply
  G.edgeFinset.card + 1 = Fintype.card V := by
-- proof
  apply StatMech.Lattice.tree_card_edges hG

/--
[connected_card_edges_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma connected_card_edges_ge_eq
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  Fintype.card V ≤ G.edgeFinset.card + 1 := by
-- proof
  apply StatMech.Lattice.connected_card_edges_ge hG

/--
[connected_card_edges_eq_iff_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma connected_card_edges_eq_iff_isAcyclic_eq
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  G.edgeFinset.card + 1 = Fintype.card V ↔ G.IsAcyclic := by
-- proof
  apply StatMech.Lattice.connected_card_edges_eq_iff_isAcyclic hG

/--
[connected_isTree_iff_card_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma connected_isTree_iff_card_edges_eq
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  G.IsTree ↔ G.edgeFinset.card + 1 = Fintype.card V := by
-- proof
  apply StatMech.Lattice.connected_isTree_iff_card_edges hG

/--
[exists_spanning_tree_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma exists_spanning_tree_card_eq
  {G : SimpleGraph V}
  [Finite V]
-- given
  (hG : G.Connected) :
-- imply
  ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ Nat.card T.edgeSet + 1 = Nat.card V := by
-- proof
  apply StatMech.Lattice.exists_spanning_tree_card hG

/--
[cyclomaticNumber_eq_zero_iff_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma cyclomaticNumber_eq_zero_iff_isAcyclic_eq
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  cyclomaticNumber G = 0 ↔ G.IsAcyclic := by
-- proof
  apply StatMech.Lattice.cyclomaticNumber_eq_zero_iff_isAcyclic hG

/--
[card_edges_eq_cyclomaticNumber_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma card_edges_eq_cyclomaticNumber_add_eq
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  G.edgeFinset.card + 1 = Fintype.card V + cyclomaticNumber G := by
-- proof
  apply StatMech.Lattice.card_edges_eq_cyclomaticNumber_add hG

/--
[not_isAcyclic_iff_exists_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma not_isAcyclic_iff_exists_cycle_eq
  {G : SimpleGraph V} :
-- imply
  ¬ G.IsAcyclic ↔ ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
-- proof
  apply StatMech.Lattice.not_isAcyclic_iff_exists_cycle

/--
[cyclomaticNumber_pos_iff_exists_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean)
-/
@[path]
private lemma cyclomaticNumber_pos_iff_exists_cycle_eq
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  0 < cyclomaticNumber G ↔ ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
-- proof
  apply StatMech.Lattice.cyclomaticNumber_pos_iff_exists_cycle hG


-- created on 2026-10-23
