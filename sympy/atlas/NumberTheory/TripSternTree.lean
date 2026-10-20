/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean -/

import Mathlib.Data.Finset.Basic

namespace MetaMathlibExt

/-- The TRIP-Stern tree for a fixed pair of source transitions induced by `F_0`
and `F_1`: a distinguished root seed together with a fixed left transition and
a fixed right transition on node values. A left edge is represented by `false`
and a right edge by `true`.

Source: Ilya Amburg, Krishna Dasaratha, Laure Flapan, Thomas Garrity, Chansoo Lee, Cornelia Mihaila,
Nicholas Neumann-Chun, Sarah Peluse, and Matthew Stoffregen, *Stern Sequences for a Family of
Multidimensional Continued Fractions: TRIP-Stern Sequences*, Journal of Integer Sequences 20 (2017),
Article 17.1.7, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Garrity/garrity6.tex>. The tree
abstracts Definition TRIPSternDef, lines 471-481 (seed (1,1,1), even/odd recursion by F_0/F_1,
levels as index intervals), with F_0/F_1 from line 387; binary paths follow the triangle(v)
definition, lines 485-488. -/
structure TripSternTree (α : Type _) where
  /-- Distinguished root seed of the tree. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
  (2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
  seed : α
  /-- Fixed left transition (induced by `F_0`), taken on a `false` edge.
  Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
  TRIPSternDef, lines 471-481. -/
  leftTransition : α → α
  /-- Fixed right transition (induced by `F_1`), taken on a `true` edge.
  Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
  TRIPSternDef, lines 471-481. -/
  rightTransition : α → α

/-- A finite binary path selects a node by iterating the corresponding
transitions from the seed: `false` takes the left transition, `true` takes the
right transition.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
TRIPSternDef, lines 471-481. -/
def TripSternTree.nodeAtPath {α : Type _} (T : TripSternTree α)
    (path : List Bool) : α :=
  path.foldl (fun node bit =>
    if bit then T.rightTransition node else T.leftTransition node) T.seed

/-- The empty path selects the root seed. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodeAtEmptyPath {α : Type _} (T : TripSternTree α) :
    T.nodeAtPath [] = T.seed :=
  rfl

/-- Appending one left step applies the left transition to the node at the
prefix path. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7,
Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodeAtPathAppendLeft {α : Type _}
    (T : TripSternTree α) (path : List Bool) :
    T.nodeAtPath (path ++ [false]) = T.leftTransition (T.nodeAtPath path) := by
  unfold TripSternTree.nodeAtPath
  rw [List.foldl_append]
  simp

/-- Appending one right step applies the right transition to the node at the
prefix path. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7,
Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodeAtPathAppendRight {α : Type _}
    (T : TripSternTree α) (path : List Bool) :
    T.nodeAtPath (path ++ [true]) = T.rightTransition (T.nodeAtPath path) := by
  unfold TripSternTree.nodeAtPath
  rw [List.foldl_append]
  simp

/-- Depth `n` consists of all nodes selected by binary paths of length `n`.
Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
TRIPSternDef, lines 471-481. -/
def TripSternTree.nodesAtDepth {α : Type _} (T : TripSternTree α)
    (n : ℕ) : Set α :=
  { y | ∃ path : List Bool, path.length = n ∧ T.nodeAtPath path = y }

/-- Membership characterization of a level. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodeMembershipAtDepth {α : Type _} (T : TripSternTree α)
    (n : ℕ) (y : α) :
    y ∈ T.nodesAtDepth n ↔
      ∃ path : List Bool, path.length = n ∧ T.nodeAtPath path = y :=
  Iff.rfl

/-- Depth zero contains exactly the root seed. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodesAtDepthZero {α : Type _}
    (T : TripSternTree α) (y : α) :
    y ∈ T.nodesAtDepth 0 ↔ y = T.seed := by
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

/-- The left-most node at depth `n`, obtained by repeatedly applying the left
transition `n` times starting from the seed. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
def TripSternTree.leftmostNode {α : Type _} (T : TripSternTree α) : ℕ → α
  | 0 => T.seed
  | n + 1 => T.leftTransition (T.leftmostNode n)

/-- The right-most node at depth `n`, obtained by repeatedly applying the right
transition `n` times starting from the seed. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
def TripSternTree.rightmostNode {α : Type _} (T : TripSternTree α) : ℕ → α
  | 0 => T.seed
  | n + 1 => T.rightTransition (T.rightmostNode n)

/-- The left-most node at depth zero is the seed. Source: Amburg et al., *TRIP-Stern Sequences*, JIS
20 (2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.leftmostNodeAtZero {α : Type _} (T : TripSternTree α) :
    T.leftmostNode 0 = T.seed :=
  rfl

/-- The left-most node at depth `n + 1` is the left transition of the left-most
node at depth `n`. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7,
Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.leftmostNodeAtSuccessor {α : Type _} (T : TripSternTree α)
    (n : ℕ) :
    T.leftmostNode (n + 1) = T.leftTransition (T.leftmostNode n) :=
  rfl

/-- The right-most node at depth zero is the seed. Source: Amburg et al., *TRIP-Stern Sequences*,
JIS 20 (2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.rightmostNodeAtZero {α : Type _} (T : TripSternTree α) :
    T.rightmostNode 0 = T.seed :=
  rfl

/-- The right-most node at depth `n + 1` is the right transition of the
right-most node at depth `n`. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article
17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.rightmostNodeAtSuccessor {α : Type _} (T : TripSternTree α)
    (n : ℕ) :
    T.rightmostNode (n + 1) = T.rightTransition (T.rightmostNode n) :=
  rfl

end MetaMathlibExt
