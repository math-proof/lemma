import sympy.concrete.continued_fraction
import sympy.Basic
import Lemma.Finset.All_EqAlphaAppend_DivHK.of.All_Gt_0
open Finset Continuant


@[main]
private lemma main
-- given
  (x : ℕ → ℝ)
  (h : ∀ i, 0 < x i)
  (n : ℕ) :
-- imply
  alpha ((List.range (n + 1)).map x) = H x (n + 1) / K x (n + 1) := by
-- proof
  cases n with
  | zero => simp [alpha, H, K]
  | succ n =>
    rw [List.range_succ (n := n + 1), List.map_append]
    exact All_EqAlphaAppend_DivHK.of.All_Gt_0 x h n (h (n + 1))


-- created on 2026-10-07
