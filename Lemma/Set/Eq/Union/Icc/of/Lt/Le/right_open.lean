import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₁ : a < x)
  (h₂ : x ≤ b) :
-- imply
  Set.Ioo a x ∪ Set.Icc x b = Set.Ioc a b := by
-- proof
  exact Set.Ioo_union_Icc_eq_Ioc h₁ h₂


-- created on 2021-02-20
-- updated on 2026-10-26
