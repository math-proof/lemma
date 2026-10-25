import Mathlib
import sympy.Basic
import Def.Combinatorics.SimpleGraph.BookNumber
open SimpleGraph


namespace SimpleGraph

/--
[le_bookNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/BookNumber.lean)
-/
@[path]
lemma le_bookNumber
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {u v : V}
-- given
  (h : G.Adj u v) :
-- imply
  (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ G.bookNumber := by
-- proof
  unfold bookNumber
  have hle := Finset.le_sup (s := (Finset.univ : Finset (V × V)))
    (f := fun p : V × V =>
      if G.Adj p.1 p.2 then
        (Finset.univ.filter fun w => G.Adj p.1 w ∧ G.Adj p.2 w).card
      else 0)
    (Finset.mem_univ (u, v))
  simpa [h] using hle

end SimpleGraph

namespace SimpleGraph

/--
[bookNumber_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/BookNumber.lean)
-/
@[path]
lemma bookNumber_le
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {b : ℕ}
-- given
  (h : ∀ u v : V, G.Adj u v → (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ b) :
-- imply
  G.bookNumber ≤ b := by
-- proof
  unfold bookNumber
  apply Finset.sup_le
  rintro ⟨u, v⟩ -
  by_cases hadj : G.Adj u v
  · simpa [hadj] using h u v hadj
  · simp [hadj]

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
