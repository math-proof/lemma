import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n a : ℝ}
-- given
  (h₀ : n ∉ Set.Iic a) :
-- imply
  n > a := by
-- proof
  simpa [Set.mem_Iic] using h₀


-- created on 2021-09-03
-- updated on 2026-10-26
