import Lemma.Basic


@[main]
private lemma fin
  [DecidableEq α]
  {s U : Finset α}
  {x : α}
-- given
  (h : x ∈ U \ s) :
-- imply
  x ∈ U := by
-- proof
  simp_all


@[main]
private lemma main
  {s U : Set α}
  {x : α}
-- given
  (h : x ∈ U \ s) :
-- imply
  x ∈ U := by
-- proof
  -- Decompose the hypothesis `h : x ∈ U \ s` into `x ∈ U` and `x ∉ s`
  let ⟨hU, hs⟩ := h
  -- Use the first part `x ∈ U` to conclude the proof
  exact hU


-- created on 2025-04-06
