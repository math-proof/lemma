import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n a : ℝ}
-- given
  (h₀ : n ∉ Set.Iio a) :
-- imply
  n ≥ a := by
-- proof
  simpa [Set.mem_Iio] using h₀


-- created on 2021-09-24
-- updated on 2026-10-26
