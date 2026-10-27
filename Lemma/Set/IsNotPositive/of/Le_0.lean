import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ≤ 0) :
-- imply
  x ∈ Set.Iic 0 :=
-- proof
  Set.mem_Iic.mpr h₀


-- created on 2021-02-15
-- updated on 2026-10-26
