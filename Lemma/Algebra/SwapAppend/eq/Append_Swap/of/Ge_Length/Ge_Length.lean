import stdlib.List
import Lemma.Algebra.SwapAppend.eq.Append_Swap
import Lemma.Algebra.EqAdd_Sub.of.Ge
open Algebra


@[main]
private lemma main
  {a : List α}
  {i j : ℕ}
-- given
  (h₀ : i ≥ a.length)
  (h₁ : j ≥ a.length)
  (b : List α) :
-- imply
  (a ++ b).swap i j = a ++ b.swap (i - a.length) (j - a.length) := by
-- proof
  have := SwapAppend.eq.Append_Swap a b (i - a.length) (j - a.length)
  rw [EqAdd_Sub.of.Ge h₀] at this
  rw [EqAdd_Sub.of.Ge h₁] at this
  assumption


-- created on 2025-06-10
