import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.BookNumber
open SimpleGraph


/--
[le_bookNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/BookNumber.lean)
-/
@[path]
private lemma le_bookNumber_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {u v : V}
-- given
  (h : G.Adj u v) :
-- imply
  (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ G.bookNumber := by
-- proof
  apply SimpleGraph.le_bookNumber h

/--
[bookNumber_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/BookNumber.lean)
-/
@[path]
private lemma bookNumber_le_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {b : ℕ}
-- given
  (h : ∀ u v : V, G.Adj u v → (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ b) :
-- imply
  G.bookNumber ≤ b := by
-- proof
  apply SimpleGraph.bookNumber_le b h


-- created on 2026-10-20
