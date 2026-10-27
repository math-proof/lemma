import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc17menger.Part4
open StatMech StatMech.Walls


/--
[bc17_exists_finInj_of_le_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_exists_finInj_of_le_ncard_eq
  {V : Type u}
  [DecidableEq V]
  {s : Set V}
  {k : ℕ}
-- given
  (hs : s.Finite)
  (hk : k ≤ s.ncard) :
-- imply
  ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, f i ∈ s := by
-- proof
  apply StatMech.Walls.bc17_exists_finInj_of_le_ncard hs hk

/--
[bc17_inter_isSeparator_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_inter_isSeparator_bot_eq
  {V : Type u}
  [DecidableEq V]
  {A B : Set V} :
-- imply
  bc16_IsSeparator (⊥ : SimpleGraph V) A B (A ∩ B) := by
-- proof
  apply StatMech.Walls.bc17_inter_isSeparator_bot A B

/--
[bc17_hard_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_hard_bot_eq
  {V : Type u}
  [DecidableEq V]
  [Fintype V]
  {A B : Set V}
  {k : ℕ}
-- given
  (hsep : ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → k ≤ C.ncard) :
-- imply
  Nonempty (bc16_DisjointPathFamily (⊥ : SimpleGraph V) A B (Fin k)) := by
-- proof
  apply StatMech.Walls.bc17_hard_bot A B hsep

/--
[bc17_edgeSet_ncard_lt_of_deleteEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_edgeSet_ncard_lt_of_deleteEdge_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype V]
  {x y : V}
-- given
  (h : G.Adj x y) :
-- imply
  (G.deleteEdges {s(x, y)}).edgeSet.ncard < G.edgeSet.ncard := by
-- proof
  apply StatMech.Walls.bc17_edgeSet_ncard_lt_of_deleteEdge h

/--
[bc17_insert_isSeparator_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_insert_isSeparator_left_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B Y : Set V}
  {x y : V}
-- given
  (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
-- imply
  bc16_IsSeparator G A B (insert x Y) := by
-- proof
  apply StatMech.Walls.bc17_insert_isSeparator_left hY

/--
[bc17_insert_isSeparator_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_insert_isSeparator_right_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B Y : Set V}
  {x y : V}
-- given
  (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
-- imply
  bc16_IsSeparator G A B (insert y Y) := by
-- proof
  apply StatMech.Walls.bc17_insert_isSeparator_right hY

/--
[bc17_endpoints_notMem_of_not_isSeparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_endpoints_notMem_of_not_isSeparator_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B Y : Set V}
  {x y : V}
-- given
  (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y)
  (hnotG : ¬ bc16_IsSeparator G A B Y) :
-- imply
  x ∉ Y ∧ y ∉ Y := by
-- proof
  apply StatMech.Walls.bc17_endpoints_notMem_of_not_isSeparator hY hnotG

/--
[bc17_deleteEdge_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_deleteEdge_dichotomy_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype V]
  {A B : Set V}
  {x y : V}
  {k : ℕ}
-- given
  (hxy : G.Adj x y)
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) :
-- imply
  (∀ C, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B C → k ≤ C.ncard) ∨ (∃ Y : Set V, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y ∧ Y.ncard < k ∧ x ∉ Y ∧ y ∉ Y ∧ bc16_IsSeparator G A B (insert x Y) ∧ bc16_IsSeparator G A B (insert y Y)) := by
-- proof
  apply StatMech.Walls.bc17_deleteEdge_dichotomy hxy hmin

/--
[bc17_hard_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_hard_zero_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {A B : Set V} :
-- imply
  Nonempty (bc16_DisjointPathFamily G A B (Fin 0)) := by
-- proof
  apply StatMech.Walls.bc17_hard_zero G A B

/--
[bc17_hard_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_hard_one_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {A B : Set V}
-- given
  (hmin : ∀ C, bc16_IsSeparator G A B C → 1 ≤ C.ncard) :
-- imply
  Nonempty (bc16_DisjointPathFamily G A B (Fin 1)) := by
-- proof
  apply StatMech.Walls.bc17_hard_one G A B hmin

/--
[bc17_hardDir_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_hardDir_bot_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype V]
  {A B : Set V} :
-- imply
  bc17_HardDir (⊥ : SimpleGraph V) A B := by
-- proof
  apply StatMech.Walls.bc17_hardDir_bot A B

/--
[bc17_hardDir_step_case1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_hardDir_step_case1_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {A B : Set V}
  {x y : V}
  {k : ℕ}
-- given
  (hH : bc17_HardDir (G.deleteEdges {s(x, y)}) A B)
  (hC1 : ∀ C, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B C → k ≤ C.ncard) :
-- imply
  Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
-- proof
  apply StatMech.Walls.bc17_hardDir_step_case1 hH hC1

/--
[bc17_restr_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_restr_adj_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {W : Set V}
  {u v : V} :
-- imply
  (bc17_restr G W).Adj u v ↔ G.Adj u v ∧ u ∈ W ∧ v ∈ W := by
-- proof
  apply StatMech.Walls.bc17_restr_adj G W

/--
[bc17_restr_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_restr_le_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {W : Set V} :
-- imply
  bc17_restr G W ≤ G := by
-- proof
  apply StatMech.Walls.bc17_restr_le G W

/--
[bc17_restr_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_restr_support_subset_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {W : Set V}
  {a b : V}
  {p : (bc17_restr G W).Walk a b}
-- given
  (ha : a ∈ W) :
-- imply
  ∀ z ∈ p.support, z ∈ W := by
-- proof
  apply StatMech.Walls.bc17_restr_support_subset G W ha p

/--
[bc17_restr_edgeSet_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_restr_edgeSet_subset_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {W : Set V} :
-- imply
  (bc17_restr G W).edgeSet ⊆ G.edgeSet := by
-- proof
  apply StatMech.Walls.bc17_restr_edgeSet_subset G W

/--
[bc17_restr_edgeSet_ncard_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_restr_edgeSet_ncard_lt_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype V]
  {G : SimpleGraph V}
  {W : Set V}
  {x y : V}
-- given
  (hxy : G.Adj x y)
  (hy : y ∉ W) :
-- imply
  (bc17_restr G W).edgeSet.ncard < G.edgeSet.ncard := by
-- proof
  apply StatMech.Walls.bc17_restr_edgeSet_ncard_lt G W hxy hy

/--
[bc17_minmax_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_minmax_one_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype V]
  {G : SimpleGraph V}
  {A B : Set V}
-- given
  (hmin : ∀ C, bc16_IsSeparator G A B C → 1 ≤ C.ncard) :
-- imply
  ∃ F : bc16_DisjointPathFamily G A B (Fin 1), ∀ C, bc16_IsSeparator G A B C → Fintype.card (Fin 1) ≤ C.ncard := by
-- proof
  apply StatMech.Walls.bc17_minmax_one G A B hmin

/--
[bc17_minmax_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean)
-/
@[path]
private lemma bc17_minmax_bot_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype V]
  {A B : Set V}
  {k : ℕ}
-- given
  (hmin : ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → k ≤ C.ncard) :
-- imply
  ∃ F : bc16_DisjointPathFamily (⊥ : SimpleGraph V) A B (Fin k), ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → Fintype.card (Fin k) ≤ C.ncard := by
-- proof
  apply StatMech.Walls.bc17_minmax_bot A B hmin


-- created on 2026-10-23
