import sympy.tensor.index_of
import sympy.Basic
open IndexOf


@[path]
private lemma main
  [DecidableEq α]
  {v : α}
  {x : ℕ → α}
  {n : ℕ}
-- given
  (h : ∃ j < n, x j = v) :
-- imply
  x (index v x n) = v := by
-- proof
  obtain ⟨j, hj, rfl⟩ := h
  have hm : x j ∈ (List.range n).map x := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have e := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
  simp only [List.getElem_map, List.getElem_range] at e
  exact e


-- created on 2026-10-07
