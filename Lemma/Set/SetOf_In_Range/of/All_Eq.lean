import Initialize.Tactic.Attr.Basic
import Theorem.Data.Set.Sets


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → α}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  {f i | i ∈ range n} = {g i | i ∈ range n} := by
-- proof
  try simp only [← Finset.mem_range] at *
  apply Set.image_congr
  intro i hi
  apply h
  exact Finset.mem_coe.mp hi


-- created on 2020-07-24
-- updated on 2026-10-26
