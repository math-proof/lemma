import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.TripSternTree
open MetaMathlibExt


namespace MetaMathlibExt

/--
[TripSternTree.nodeAtEmptyPath](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.nodeAtEmptyPath
  {T : TripSternTree α} :
-- imply
  T.nodeAtPath [] = T.seed :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[TripSternTree.nodeAtPathAppendLeft](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.nodeAtPathAppendLeft
  {T : TripSternTree α}
  {path : List Bool} :
-- imply
  T.nodeAtPath (path ++ [false]) = T.leftTransition (T.nodeAtPath path) := by
-- proof
  unfold TripSternTree.nodeAtPath
  rw [List.foldl_append]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[TripSternTree.nodeAtPathAppendRight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.nodeAtPathAppendRight
  {T : TripSternTree α}
  {path : List Bool} :
-- imply
  T.nodeAtPath (path ++ [true]) = T.rightTransition (T.nodeAtPath path) := by
-- proof
  unfold TripSternTree.nodeAtPath
  rw [List.foldl_append]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[TripSternTree.nodeMembershipAtDepth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.nodeMembershipAtDepth
  {T : TripSternTree α}
  {n : ℕ}
  {y : α} :
-- imply
  y ∈ T.nodesAtDepth n ↔
    ∃ path : List Bool, path.length = n ∧ T.nodeAtPath path = y :=
-- proof
  Iff.rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[TripSternTree.nodesAtDepthZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.nodesAtDepthZero
  {T : TripSternTree α}
  {y : α} :
-- imply
  y ∈ T.nodesAtDepth 0 ↔ y = T.seed := by
-- proof
  constructor
  · intro h
    match h with
    | ⟨path, hlen, hnode⟩ =>
      rw [List.length_eq_zero_iff] at hlen
      subst hlen
      simp [TripSternTree.nodeAtPath] at hnode
      exact hnode.symm
  · intro h
    subst h
    exact ⟨[], rfl, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[TripSternTree.leftmostNodeAtZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.leftmostNodeAtZero
  {T : TripSternTree α} :
-- imply
  T.leftmostNode 0 = T.seed :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[TripSternTree.leftmostNodeAtSuccessor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.leftmostNodeAtSuccessor
  {T : TripSternTree α}
  {n : ℕ} :
-- imply
  T.leftmostNode (n + 1) = T.leftTransition (T.leftmostNode n) :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[TripSternTree.rightmostNodeAtZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.rightmostNodeAtZero
  {T : TripSternTree α} :
-- imply
  T.rightmostNode 0 = T.seed :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[TripSternTree.rightmostNodeAtSuccessor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
lemma TripSternTree.rightmostNodeAtSuccessor
  {T : TripSternTree α}
  {n : ℕ} :
-- imply
  T.rightmostNode (n + 1) = T.rightTransition (T.rightmostNode n) :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
