import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
open StatMech StatMech.Walls


/--
[bc18_firstHit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_firstHit_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Set V}
  {a b : V}
  {p : G.Walk a b} :
-- imply
  (∃ z ∈ p.support, z ∈ S) → ∃ (c : V) (q : G.Walk a c), c ∈ S ∧ q.support ⊆ p.support ∧ (∀ z ∈ q.support, z ∈ S → z = c) := by
-- proof
  apply StatMech.Walls.bc18_firstHit p

/--
[bc18_firstHitPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_firstHitPath_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Set V}
  {a b : V}
  {p : G.Walk a b}
-- given
  (hmem : ∃ z ∈ p.support, z ∈ S) :
-- imply
  ∃ (c : V) (q : G.Walk a c), q.IsPath ∧ c ∈ S ∧ q.support ⊆ p.support ∧ (∀ z ∈ q.support, z ∈ S → z = c) := by
-- proof
  apply StatMech.Walls.bc18_firstHitPath p hmem

/--
[bc18_subset_AReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_subset_AReach_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {A S : Set V} :
-- imply
  A ⊆ bc18_AReach G A S := by
-- proof
  apply StatMech.Walls.bc18_subset_AReach G A S

/--
[bc18_mem_AReach_of_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_mem_AReach_of_mem_support_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A S : Set V}
  {a v : V}
  {q : G.Walk a v}
  {z : V}
-- given
  (ha : a ∈ A)
  (hqpath : q.IsPath)
  (hq : ∀ z ∈ q.support, z ∈ S → z = v)
  (hz : z ∈ q.support) :
-- imply
  z ∈ bc18_AReach G A S := by
-- proof
  apply StatMech.Walls.bc18_mem_AReach_of_mem_support ha hqpath hq hz

/--
[bc18_AReach_separator_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_AReach_separator_transfer_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B S C : Set V}
-- given
  (hS : bc16_IsSeparator G A B S)
  (hC : bc16_IsSeparator (bc17_restr G (bc18_AReach G A S)) A S C) :
-- imply
  bc16_IsSeparator G A B C := by
-- proof
  apply StatMech.Walls.bc18_AReach_separator_transfer hS hC

/--
[bc18_splitAtEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_splitAtEdge_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {K : SimpleGraph V}
  {x y a₀ b₀ : V}
  {R : K.Walk a₀ b₀} :
-- imply
  (K.deleteEdges {s(x, y)}).Reachable a₀ b₀ ∨ ((K.deleteEdges {s(x, y)}).Reachable a₀ x ∧ (K.deleteEdges {s(x, y)}).Reachable y b₀) ∨ ((K.deleteEdges {s(x, y)}).Reachable a₀ y ∧ (K.deleteEdges {s(x, y)}).Reachable x b₀) := by
-- proof
  apply StatMech.Walls.bc18_splitAtEdge R

/--
[bc18_reachableRestrCompl_to_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_reachableRestrCompl_to_walk_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {Y : Set V}
  {a b : V}
-- given
  (ha : a ∉ Y)
  (h : (bc17_restr G {v | v ∉ Y}).Reachable a b) :
-- imply
  ∃ p : G.Walk a b, ∀ w ∈ p.support, w ∉ Y := by
-- proof
  apply StatMech.Walls.bc18_reachableRestrCompl_to_walk ha h

/--
[bc18_restr_compl_deleteEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_restr_compl_deleteEdges_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {Y : Set V}
  {x y : V} :
-- imply
  (bc17_restr G {v | v ∉ Y}).deleteEdges {s(x, y)} = bc17_restr (G.deleteEdges {s(x, y)}) {v | v ∉ Y} := by
-- proof
  apply StatMech.Walls.bc18_restr_compl_deleteEdges

/--
[bc18_areach_to_reachable_del](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_areach_to_reachable_del_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A Y : Set V}
  {c x y z : V}
-- given
  (hz : z ∈ bc18_AReach G A (insert c Y))
  (hzS : z ∉ insert c Y)
  (hc : c = x ∨ c = y) :
-- imply
  ∃ a ∈ A, a ∉ Y ∧ (bc17_restr (G.deleteEdges {s(x, y)}) {v | v ∉ Y}).Reachable a z := by
-- proof
  apply StatMech.Walls.bc18_areach_to_reachable_del hz hzS hc

/--
[bc18_contra_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_contra_of_reachable_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B Y : Set V}
  {x y a b : V}
-- given
  (hYsep : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y)
  (ha : a ∈ A)
  (hb : b ∈ B)
  (haY : a ∉ Y)
  (h : (bc17_restr (G.deleteEdges {s(x, y)}) {v | v ∉ Y}).Reachable a b) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc18_contra_of_reachable hYsep ha hb haY h

/--
[bc18_notBoth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_notBoth_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B Y : Set V}
  {x y : V}
-- given
  (hxy : G.Adj x y)
  (hxY : x ∉ Y)
  (hyY : y ∉ Y)
  (hYsep : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y)
  (hYnotG : ¬ bc16_IsSeparator G A B Y) :
-- imply
  ¬ (y ∈ bc18_AReach G A (insert x Y) ∧ x ∈ bc18_AReach G A (insert y Y)) := by
-- proof
  apply StatMech.Walls.bc18_notBoth hxy hxY hyY hYsep hYnotG

/--
[bc18_AReach_inter_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_AReach_inter_subset_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B S : Set V}
-- given
  (hS : bc16_IsSeparator G A B S) :
-- imply
  bc18_AReach G A S ∩ bc18_AReach G B S ⊆ S := by
-- proof
  apply StatMech.Walls.bc18_AReach_inter_subset hS

/--
[bc18_mem_AReach_of_essential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_mem_AReach_of_essential_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B S : Set V}
  {w : V}
-- given
  (hSsep : bc16_IsSeparator G A B S)
  (hnotSep : ¬ bc16_IsSeparator G A B (S \ {w})) :
-- imply
  w ∈ bc18_AReach G A S := by
-- proof
  apply StatMech.Walls.bc18_mem_AReach_of_essential hSsep hnotSep

/--
[bc18_appendPath_of_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_appendPath_of_inter_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {a v b : V}
  {p : G.Walk a v}
  {q : G.Walk v b}
-- given
  (hp : p.IsPath)
  (hq : q.IsPath)
  (hint : ∀ z, z ∈ p.support → z ∈ q.support → z = v) :
-- imply
  (p.append q).IsPath := by
-- proof
  apply StatMech.Walls.bc18_appendPath_of_inter hp hq hint

/--
[bc18_aside_fan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean)
-/
@[path]
private lemma bc18_aside_fan_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B S : Set V}
  {k : ℕ}
-- given
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
  (hSsep : bc16_IsSeparator G A B S)
  (hH : bc17_HardDir (bc17_restr G (bc18_AReach G A S)) A S) :
-- imply
  Nonempty (bc16_DisjointPathFamily (bc17_restr G (bc18_AReach G A S)) A S (Fin k)) := by
-- proof
  apply StatMech.Walls.bc18_aside_fan hmin hSsep hH


-- created on 2026-10-23
