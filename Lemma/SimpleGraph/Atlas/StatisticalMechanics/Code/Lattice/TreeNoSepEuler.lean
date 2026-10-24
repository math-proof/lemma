import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.TreeNoSepEuler
open SimpleGraph Set StatMech StatMech.Lattice


/--
[tnse_connected_of_card_components_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_connected_of_card_components_eq_one_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hcard : Nat.card G.ConnectedComponent = 1) :
-- imply
  G.Connected := by
-- proof
  apply StatMech.Lattice.tnse_connected_of_card_components_eq_one hcard

/--
[tnse_connected_deleteEdge_of_nonbridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_connected_deleteEdge_of_nonbridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {a b : V}
-- given
  (hA : A.Connected)
  (he : s(a, b) ∈ A.edgeSet)
  (hr : (A.deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  (A.deleteEdges {s(a, b)}).Connected := by
-- proof
  apply StatMech.Lattice.tnse_connected_deleteEdge_of_nonbridge A hA he hr

/--
[tnse_connected_deleteEdge_of_isNonBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_connected_deleteEdge_of_isNonBridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {e : Sym2 V}
-- given
  (hA : A.Connected)
  (he : tnse_IsNonBridgeEdge A e) :
-- imply
  (A.deleteEdges {e}).Connected := by
-- proof
  apply StatMech.Lattice.tnse_connected_deleteEdge_of_isNonBridge A hA he

/--
[tnse_deleteList_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_deleteList_nil_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V} :
-- imply
  tnse_deleteList A [] = A := by
-- proof
  apply StatMech.Lattice.tnse_deleteList_nil A

/--
[tnse_deleteList_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_deleteList_cons_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {e : Sym2 V}
  {L : List (Sym2 V)} :
-- imply
  tnse_deleteList A (e :: L) = (tnse_deleteList A L).deleteEdges {e} := by
-- proof
  apply StatMech.Lattice.tnse_deleteList_cons A e L

/--
[tnse_allNonBridge_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_allNonBridge_nil_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V} :
-- imply
  tnse_AllNonBridge A [] := by
-- proof
  apply StatMech.Lattice.tnse_allNonBridge_nil A

/--
[tnse_allNonBridge_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_allNonBridge_cons_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {e : Sym2 V}
  {L : List (Sym2 V)}
-- given
  (hhead : tnse_IsNonBridgeEdge (tnse_deleteList A L) e)
  (htail : tnse_AllNonBridge A L) :
-- imply
  tnse_AllNonBridge A (e :: L) := by
-- proof
  apply StatMech.Lattice.tnse_allNonBridge_cons hhead htail

/--
[tnse_connected_deleteList_of_allNonBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_connected_deleteList_of_allNonBridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {L : List (Sym2 V)}
-- given
  (hA : A.Connected)
  (hnb : tnse_AllNonBridge A L) :
-- imply
  (tnse_deleteList A L).Connected := by
-- proof
  apply StatMech.Lattice.tnse_connected_deleteList_of_allNonBridge A hA hnb

/--
[tnse_reachable_of_detour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_reachable_of_detour_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {a b a' b' : V}
-- given
  (h0 : A.Adj a a')
  (h1 : A.Adj a' b')
  (h2 : A.Adj b' b)
  (hne1 : s(a, a') ≠ s(a, b))
  (hne2 : s(a', b') ≠ s(a, b))
  (hne3 : s(b', b) ≠ s(a, b)) :
-- imply
  (A.deleteEdges {s(a, b)}).Reachable a b := by
-- proof
  apply StatMech.Lattice.tnse_reachable_of_detour A h0 h1 h2 hne1 hne2 hne3

/--
[tnse_grid_edge_nonbridge_of_detour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_grid_edge_nonbridge_of_detour_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {a b a' b' : V}
-- given
  (hab : s(a, b) ∈ A.edgeSet)
  (h0 : A.Adj a a')
  (h1 : A.Adj a' b')
  (h2 : A.Adj b' b)
  (hne1 : s(a, a') ≠ s(a, b))
  (hne2 : s(a', b') ≠ s(a, b))
  (hne3 : s(b', b) ≠ s(a, b)) :
-- imply
  tnse_IsNonBridgeEdge A s(a, b) := by
-- proof
  apply StatMech.Lattice.tnse_grid_edge_nonbridge_of_detour A hab h0 h1 h2 hne1 hne2 hne3

/--
[tnse_site_ne_of_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_site_ne_of_col_eq
  [Empty.Finite V]
  [DecidableEq V]
  {x y x' y' : ℤ}
-- given
  (h : x ≠ x') :
-- imply
  (![x, y] : Site 2) ≠ ![x', y'] := by
-- proof
  apply StatMech.Lattice.tnse_site_ne_of_col h

/--
[tnse_site_ne_of_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_site_ne_of_row_eq
  [Empty.Finite V]
  [DecidableEq V]
  {x y x' y' : ℤ}
-- given
  (h : y ≠ y') :
-- imply
  (![x, y] : Site 2) ≠ ![x', y'] := by
-- proof
  apply StatMech.Lattice.tnse_site_ne_of_row h

/--
[tnse_horizEdge_nonbridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_horizEdge_nonbridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {R : ℕ}
  {x y : ℤ}
-- given
  (hx : x.natAbs ≤ R)
  (hx1 : (x + 1).natAbs ≤ R)
  (hy : y.natAbs ≤ R)
  (hy1 : (y + 1).natAbs ≤ R) :
-- imply
  tnse_IsNonBridgeEdge (boxInduce R) s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)), (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R))) := by
-- proof
  apply StatMech.Lattice.tnse_horizEdge_nonbridge hx hx1 hy hy1

/--
[tnse_deleteList_adj_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_deleteList_adj_of_notMem_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {c d : V}
-- given
  (h : A.Adj c d) :
-- imply
  ∀ {L : List (Sym2 V)}, s(c, d) ∉ L → (tnse_deleteList A L).Adj c d := by
-- proof
  apply StatMech.Lattice.tnse_deleteList_adj_of_notMem h

/--
[tnse_nonbridge_of_detour_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_nonbridge_of_detour_notMem_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {a b a' b' : V}
  {L : List (Sym2 V)}
-- given
  (hab : s(a, b) ∈ (tnse_deleteList A L).edgeSet)
  (h0 : A.Adj a a')
  (h1 : A.Adj a' b')
  (h2 : A.Adj b' b)
  (hne1 : s(a, a') ≠ s(a, b))
  (hne2 : s(a', b') ≠ s(a, b))
  (hne3 : s(b', b) ≠ s(a, b))
  (hL1 : s(a, a') ∉ L)
  (hL2 : s(a', b') ∉ L)
  (hL3 : s(b', b) ∉ L) :
-- imply
  tnse_IsNonBridgeEdge (tnse_deleteList A L) s(a, b) := by
-- proof
  apply StatMech.Lattice.tnse_nonbridge_of_detour_notMem hab h0 h1 h2 hne1 hne2 hne3 hL1 hL2 hL3

/--
[tnse_allNonBridge_of_treeFreeDetour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_allNonBridge_of_treeFreeDetour_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V} :
-- imply
  ∀ {L : List (Sym2 V)}, L.Nodup → (∀ e ∈ L, tnse_HasTreeFreeDetour A L e) → tnse_AllNonBridge A L := by
-- proof
  apply StatMech.Lattice.tnse_allNonBridge_of_treeFreeDetour

/--
[tnse_box_minus_treeFreeDetour_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_box_minus_treeFreeDetour_connected_eq
  [Empty.Finite V]
  [DecidableEq V]
  {R : ℕ}
  {L : List (Sym2 ↥(box 2 R))}
-- given
  (hnodup : L.Nodup)
  (hdet : ∀ e ∈ L, tnse_HasTreeFreeDetour (boxInduce R) L e) :
-- imply
  (tnse_deleteList (boxInduce R) L).Connected := by
-- proof
  apply StatMech.Lattice.tnse_box_minus_treeFreeDetour_connected hnodup hdet

/--
[tnse_box_minus_tree_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_box_minus_tree_connected_eq
  [Empty.Finite V]
  [DecidableEq V]
  {R : ℕ}
  {L : List (Sym2 ↥(box 2 R))}
-- given
  (hnb : tnse_AllNonBridge (boxInduce R) L) :
-- imply
  (tnse_deleteList (boxInduce R) L).Connected := by
-- proof
  apply StatMech.Lattice.tnse_box_minus_tree_connected hnb

/--
[tnse_box_minus_nil_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_box_minus_nil_connected_eq
  [Empty.Finite V]
  [DecidableEq V]
  {R : ℕ} :
-- imply
  (tnse_deleteList (boxInduce R) []).Connected := by
-- proof
  apply StatMech.Lattice.tnse_box_minus_nil_connected R

/--
[tnse_box_minus_singleHorizEdge_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_box_minus_singleHorizEdge_connected_eq
  [Empty.Finite V]
  [DecidableEq V]
  {R : ℕ}
  {x y : ℤ}
-- given
  (hx : x.natAbs ≤ R)
  (hx1 : (x + 1).natAbs ≤ R)
  (hy : y.natAbs ≤ R)
  (hy1 : (y + 1).natAbs ≤ R) :
-- imply
  (tnse_deleteList (boxInduce R) [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)), (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))]).Connected := by
-- proof
  apply StatMech.Lattice.tnse_box_minus_singleHorizEdge_connected hx hx1 hy hy1

/--
[tnse_singleHorizEdge_treeFreeDetour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_singleHorizEdge_treeFreeDetour_eq
  [Empty.Finite V]
  [DecidableEq V]
  {R : ℕ}
  {x y : ℤ}
-- given
  (hx : x.natAbs ≤ R)
  (hx1 : (x + 1).natAbs ≤ R)
  (hy : y.natAbs ≤ R)
  (hy1 : (y + 1).natAbs ≤ R) :
-- imply
  ∀ e ∈ [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)), (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))], tnse_HasTreeFreeDetour (boxInduce R) [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)), (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))] e := by
-- proof
  apply StatMech.Lattice.tnse_singleHorizEdge_treeFreeDetour hx hx1 hy hy1

/--
[tnse_box_minus_singleHorizEdge_connected_orderFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_box_minus_singleHorizEdge_connected_orderFree_eq
  [Empty.Finite V]
  [DecidableEq V]
  {R : ℕ}
  {x y : ℤ}
-- given
  (hx : x.natAbs ≤ R)
  (hx1 : (x + 1).natAbs ≤ R)
  (hy : y.natAbs ≤ R)
  (hy1 : (y + 1).natAbs ≤ R) :
-- imply
  (tnse_deleteList (boxInduce R) [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)), (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))]).Connected := by
-- proof
  apply StatMech.Lattice.tnse_box_minus_singleHorizEdge_connected_orderFree hx hx1 hy hy1

/--
[tnse_singleEdge_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean)
-/
@[path]
private lemma tnse_singleEdge_nonvacuous_eq
  [Empty.Finite V]
  [DecidableEq V] :
-- imply
  (tnse_deleteList (boxInduce 2) [s((⟨![0, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)), (⟨![1, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)))]).Reachable (⟨![0, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)) (⟨![1, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)) := by
-- proof
  apply StatMech.Lattice.tnse_singleEdge_nonvacuous


-- created on 2026-10-23
