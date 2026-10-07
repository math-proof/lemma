import sympy.tensor.index_of
import sympy.Basic
open IndexOf


@[main]
private lemma main
  [DecidableEq α]
  {v : α}
  {x : ℕ → α}
  {n : ℕ}
-- given
  (h : ∃ j < n, x j = v) :
-- imply
  index v x n < n := by
-- proof
  obtain ⟨j, hj, rfl⟩ := h
  have hm : x j ∈ (List.range n).map x := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simpa [index] using List.idxOf_lt_length_of_mem hm


-- created on 2026-10-07
