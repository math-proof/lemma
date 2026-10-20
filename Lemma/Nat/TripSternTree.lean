import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.TripSternTree
open MetaMathlibExt


/--
[TripSternTree.nodeAtEmptyPath](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_nodeAtEmptyPath_eq
  {T : TripSternTree α} :
-- imply
  T.nodeAtPath [] = T.seed := by
-- proof
  apply MetaMathlibExt.TripSternTree.nodeAtEmptyPath T

/--
[TripSternTree.nodeAtPathAppendLeft](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_nodeAtPathAppendLeft_eq
  {T : TripSternTree α}
  {path : List Bool} :
-- imply
  T.nodeAtPath (path ++ [false]) = T.leftTransition (T.nodeAtPath path) := by
-- proof
  apply MetaMathlibExt.TripSternTree.nodeAtPathAppendLeft T path

/--
[TripSternTree.nodeAtPathAppendRight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_nodeAtPathAppendRight_eq
  {T : TripSternTree α}
  {path : List Bool} :
-- imply
  T.nodeAtPath (path ++ [true]) = T.rightTransition (T.nodeAtPath path) := by
-- proof
  apply MetaMathlibExt.TripSternTree.nodeAtPathAppendRight T path

/--
[TripSternTree.nodeMembershipAtDepth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_nodeMembershipAtDepth_eq
  {T : TripSternTree α}
  {n : ℕ}
  {y : α} :
-- imply
  y ∈ T.nodesAtDepth n ↔
    ∃ path : List Bool, path.length = n ∧ T.nodeAtPath path = y := by
-- proof
  apply MetaMathlibExt.TripSternTree.nodeMembershipAtDepth T n y

/--
[TripSternTree.nodesAtDepthZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_nodesAtDepthZero_eq
  {T : TripSternTree α}
  {y : α} :
-- imply
  y ∈ T.nodesAtDepth 0 ↔ y = T.seed := by
-- proof
  apply MetaMathlibExt.TripSternTree.nodesAtDepthZero T y

/--
[TripSternTree.leftmostNodeAtZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_leftmostNodeAtZero_eq
  {T : TripSternTree α} :
-- imply
  T.leftmostNode 0 = T.seed := by
-- proof
  apply MetaMathlibExt.TripSternTree.leftmostNodeAtZero T

/--
[TripSternTree.leftmostNodeAtSuccessor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_leftmostNodeAtSuccessor_eq
  {T : TripSternTree α}
  {n : ℕ} :
-- imply
  T.leftmostNode (n + 1) = T.leftTransition (T.leftmostNode n) := by
-- proof
  apply MetaMathlibExt.TripSternTree.leftmostNodeAtSuccessor T n

/--
[TripSternTree.rightmostNodeAtZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_rightmostNodeAtZero_eq
  {T : TripSternTree α} :
-- imply
  T.rightmostNode 0 = T.seed := by
-- proof
  apply MetaMathlibExt.TripSternTree.rightmostNodeAtZero T

/--
[TripSternTree.rightmostNodeAtSuccessor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean)
-/
@[path]
private lemma TripSternTree_rightmostNodeAtSuccessor_eq
  {T : TripSternTree α}
  {n : ℕ} :
-- imply
  T.rightmostNode (n + 1) = T.rightTransition (T.rightmostNode n) := by
-- proof
  apply MetaMathlibExt.TripSternTree.rightmostNodeAtSuccessor T n


-- created on 2026-10-20
