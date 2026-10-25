/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean -/

import Mathlib.Data.Finset.Basic
import Structure.NumberTheory.TripSternTree


namespace MetaMathlibExt

/-- A finite binary path selects a node by iterating the corresponding
transitions from the seed: `false` takes the left transition, `true` takes the
right transition.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
TRIPSternDef, lines 471-481. -/
def TripSternTree.nodeAtPath {α : Type _} (T : TripSternTree α)
    (path : List Bool) : α :=
  path.foldl (fun node bit =>
    if bit then T.rightTransition node else T.leftTransition node) T.seed

/-- Depth `n` consists of all nodes selected by binary paths of length `n`.
Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
TRIPSternDef, lines 471-481. -/
def TripSternTree.nodesAtDepth {α : Type _} (T : TripSternTree α)
    (n : ℕ) : Set α :=
  { y | ∃ path : List Bool, path.length = n ∧ T.nodeAtPath path = y }

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

end MetaMathlibExt
