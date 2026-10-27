import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommMonoid α]
  {k : ℕ}
  {x : Fin k → ℤ}
  {f : Fin k → ℕ}
  {h : ℤ → ℕ → α} :
-- imply
  ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < k), ∏ j ∈ Finset.range (f i), h (x i) j
    = ∏ i, ∏ j ∈ Finset.range (f i), h (x i) j := by
-- proof
  rw [Finset.filter_true_of_mem]
  intro i _
  exact i.isLt


-- created on 2020-03-03
-- updated on 2026-10-26
