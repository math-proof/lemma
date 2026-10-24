import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.OutwardArmForestClose
open Set SimpleGraph Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation StatMech.Percolation.OafTree


/--
[oaf_openSubgraph_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_openSubgraph_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  openSubgraph d (removeSite x ω) = oaf_cutGraph (openSubgraph d ω) x := by
-- proof
  apply StatMech.Percolation.oaf_openSubgraph_removeSite ω x

/--
[oaf_connected_removeSite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_connected_removeSite_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a b : Site d} :
-- imply
  Lattice.Connected d (removeSite x ω) a b ↔ (oaf_cutGraph (openSubgraph d ω) x).Reachable a b := by
-- proof
  apply StatMech.Percolation.oaf_connected_removeSite_iff ω x a b

/--
[oaf_outwardArm_false_of_rootCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_outwardArm_false_of_rootCover_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {r : Site d}
  {c : Fin 3 → Site d}
-- given
  (hrbox : r ∈ box d n)
  (htri_r : IsTrifurcation d ω r)
  (hcT : ∀ i, c i ∈ tfc_trifFinset ω n)
  (hcne : ∀ i, c i ≠ r)
  (hcover : ∀ a, Connected d ω r a → a ≠ r → ∃ i, Connected d (removeSite r ω) a (c i)) :
-- imply
  ¬ fld_OutwardArm ω n := by
-- proof
  apply StatMech.Percolation.oaf_outwardArm_false_of_rootCover ω n hrbox htri_r hcT hcne hcover

/--
[oaf_abstractForestPeel_false_of_rootCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_abstractForestPeel_false_of_rootCover_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  {T : Finset V}
  {r : V}
  {c : Fin 3 → V}
-- given
  (hrT : r ∈ T)
  (hcT : ∀ i, c i ∈ T)
  (hcne : ∀ i, c i ≠ r)
  (hcover : ∀ a, G.Reachable r a → a ∉ T → ∃ i, (oaf_cutGraph G r).Reachable a (c i)) :
-- imply
  ¬ oaf_AbstractForestPeel G T := by
-- proof
  apply StatMech.Percolation.oaf_abstractForestPeel_false_of_rootCover G T hrT hcT hcne hcover

/--
[oaf_reach_eqLabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_reach_eqLabel_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {φ : V → L}
  {x y : V}
-- given
  (hφ : ∀ a b, H.Adj a b → φ a = φ b)
  (h : H.Reachable x y) :
-- imply
  φ x = φ y := by
-- proof
  apply StatMech.Percolation.oaf_reach_eqLabel H φ hφ h

/--
[oaf_sub_const_on_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_sub_const_on_cut_eq
  {d : ℕ} :
-- imply
  ∀ a b, (oaf_cutGraph G 0).Adj a b → sub a = sub b := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_sub_const_on_cut

/--
[oaf_children_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_children_separated_eq
  {d : ℕ}
  {i j : Fin 3}
-- given
  (hij : i ≠ j) :
-- imply
  ¬ (oaf_cutGraph G 0).Reachable (child i) (child j) := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_children_separated i j hij

/--
[oaf_adj_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_adj_reach_eq
  {d : ℕ}
  {a b : V}
-- given
  (h : G.Adj a b)
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
-- imply
  (oaf_cutGraph G 0).Reachable a b := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_adj_reach h ha hb

/--
[oaf_cover_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_cover_leaf_eq
  {d : ℕ}
  {a : V}
-- given
  (haT : a ∉ Ttree) :
-- imply
  (oaf_cutGraph G 0).Reachable a (child (sub a)) := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_cover_leaf a haT

/--
[oaf_edge_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_edge_reach_eq
  {d : ℕ}
  {a b : V}
-- given
  (h : G.Adj a b) :
-- imply
  G.Reachable a b := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_edge_reach h

/--
[oaf_root_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_root_reach_eq
  {d : ℕ}
  {a : V} :
-- imply
  G.Reachable 0 a := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_root_reach a

/--
[oaf_tree_not_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_tree_not_forestPeel_eq
  {d : ℕ} :
-- imply
  ¬ oaf_AbstractForestPeel G Ttree := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_tree_not_forestPeel

/--
[oaf_root_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_root_deg_eq
  {d : ℕ} :
-- imply
  3 ≤ G.degree 0 := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_root_deg

/--
[oaf_child_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_child_deg_eq
  {d : ℕ} :
-- imply
  ∀ i : Fin 3, 3 ≤ G.degree (child i) := by
-- proof
  apply StatMech.Percolation.OafTree.oaf_child_deg

/--
[oaf_deg_pos_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_deg_pos_of_connected_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
-- given
  (hconn : G.Connected)
  (hV : 2 ≤ Fintype.card V) :
-- imply
  1 ≤ G.degree v := by
-- proof
  apply StatMech.Percolation.oaf_deg_pos_of_connected G hconn hV v

/--
[oaf_tree_internal_lt_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean)
-/
@[path]
private lemma oaf_tree_internal_lt_leaves_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hT : G.IsTree)
  (hV : 2 ≤ Fintype.card V) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card < (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Percolation.oaf_tree_internal_lt_leaves G hT hV


-- created on 2026-10-23
