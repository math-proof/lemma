import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc_agreeconst.Part2
open Finset SimpleGraph StatMech StatMech.Walls


/--
[crossesBoundary_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean)
-/
@[path]
private lemma crossesBoundary_mk_eq
  {G : SimpleGraph V}
  {S : Set V}
  {u v : V} :
-- imply
  crossesBoundary S s(u, v) ↔ (u ∈ S) ≠ (v ∈ S) := by
-- proof
  apply StatMech.Walls.crossesBoundary_mk S u v

/--
[mem_edgeBoundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean)
-/
@[path]
private lemma mem_edgeBoundary_iff_eq
  {G : SimpleGraph V}
  {S : Set V}
  (G)
  {u v : V}
-- given
  (h : G.Adj u v) :
-- imply
  s(u, v) ∈ edgeBoundary G S ↔ (u ∈ S) ≠ (v ∈ S) := by
-- proof
  apply StatMech.Walls.mem_edgeBoundary_iff S h

/--
[agree_bit_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean)
-/
@[path]
private lemma agree_bit_adj_eq
  {G : SimpleGraph V}
  {S T : Set V}
  {u v : V}
-- given
  (hbdy : edgeBoundary G S = edgeBoundary G T)
  (h : G.Adj u v) :
-- imply
  ((u ∈ S) ↔ (u ∈ T)) ↔ ((v ∈ S) ↔ (v ∈ T)) := by
-- proof
  apply StatMech.Walls.agree_bit_adj hbdy h

/--
[agree_bit_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean)
-/
@[path]
private lemma agree_bit_walk_eq
  {G : SimpleGraph V}
  {S T : Set V}
  {x y : V}
  {w : G.Walk x y}
-- given
  (hbdy : edgeBoundary G S = edgeBoundary G T) :
-- imply
  ((x ∈ S) ↔ (x ∈ T)) ↔ ((y ∈ S) ↔ (y ∈ T)) := by
-- proof
  apply StatMech.Walls.agree_bit_walk hbdy w

/--
[agree_bit_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean)
-/
@[path]
private lemma agree_bit_const_eq
  {G : SimpleGraph V}
  {S T : Set V}
  {x y : V}
-- given
  (hG : G.Preconnected)
  (hbdy : edgeBoundary G S = edgeBoundary G T) :
-- imply
  ((x ∈ S) ↔ (x ∈ T)) ↔ ((y ∈ S) ↔ (y ∈ T)) := by
-- proof
  apply StatMech.Walls.agree_bit_const hG hbdy x y

/--
[agreeBit_const_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean)
-/
@[path]
private lemma agreeBit_const_bool_eq
  {G : SimpleGraph V}
  {S T : Set V}
  [DecidablePred (· ∈ S)]
  [DecidablePred (· ∈ T)]
  {x y : V}
-- given
  (hG : G.Preconnected)
  (hbdy : edgeBoundary G S = edgeBoundary G T) :
-- imply
  (decide (x ∈ S) = decide (x ∈ T)) ↔ (decide (y ∈ S) = decide (y ∈ T)) := by
-- proof
  apply StatMech.Walls.agreeBit_const_bool hG hbdy x y

/--
[eq_or_compl_of_edgeBoundary_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean)
-/
@[path]
private lemma eq_or_compl_of_edgeBoundary_eq_eq
  {G : SimpleGraph V}
  {S T : Set V}
  [Nonempty V]
-- given
  (hG : G.Preconnected)
  (hbdy : edgeBoundary G S = edgeBoundary G T) :
-- imply
  S = T ∨ (∀ z, z ∈ S ↔ z ∉ T) := by
-- proof
  apply StatMech.Walls.eq_or_compl_of_edgeBoundary_eq hG hbdy


-- created on 2026-10-23
