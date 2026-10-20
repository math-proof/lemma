/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/BookNumber.lean -/

import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Book numbers of finite graphs

The book number of a graph is the maximum, over adjacent vertex pairs, of the
number of common neighbors (triangles sharing that edge). This is the
canonical invariant consumed by the book-triangle and Erdős Problem 80
entries.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The book number of `G`: the maximum, over adjacent ordered vertex pairs,
of the number of common neighbors (triangles sharing that edge). Nonedges
contribute zero. -/
noncomputable def bookNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup Finset.univ fun p : V × V =>
    if G.Adj p.1 p.2 then
      (Finset.univ.filter fun w => G.Adj p.1 w ∧ G.Adj p.2 w).card
    else 0

/-- The common-neighbor count at an adjacent pair is bounded by the book
number. -/
theorem le_bookNumber {u v : V} (h : G.Adj u v) :
    (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ G.bookNumber := by
  unfold bookNumber
  have hle := Finset.le_sup (s := (Finset.univ : Finset (V × V)))
    (f := fun p : V × V =>
      if G.Adj p.1 p.2 then
        (Finset.univ.filter fun w => G.Adj p.1 w ∧ G.Adj p.2 w).card
      else 0)
    (Finset.mem_univ (u, v))
  simpa [h] using hle

/-- A uniform bound on every adjacent pair's common-neighbor count bounds the
book number. -/
theorem bookNumber_le (b : ℕ)
    (h : ∀ u v : V, G.Adj u v →
      (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ b) :
    G.bookNumber ≤ b := by
  unfold bookNumber
  apply Finset.sup_le
  rintro ⟨u, v⟩ -
  by_cases hadj : G.Adj u v
  · simpa [hadj] using h u v hadj
  · simp [hadj]

end SimpleGraph
