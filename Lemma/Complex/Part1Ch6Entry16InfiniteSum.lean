import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch6Entry16InfiniteSum

open Ramanujan.Part1Ch6.Entry16InfiniteSum

/--
[Part1Ch6Entry16InfiniteSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry16InfiniteSum.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry16_infinite_sum_eq
-- given
  (a r x : ℂ)
  (hr : ‖r‖ < 1)
  (hx : ‖x‖ ≤ 1)
  (hboundary : ‖x‖ = 1 → ‖a * r‖ < 1)
  (hpoles : ∀ k : ℕ, 1 ≤ k → 1 - a * x ^ k ≠ 0)
  (hboundarySeparated : ‖x‖ = 1 → ∃ delta : ℝ, 0 < delta ∧ ∀ k : ℕ, 1 ≤ k → delta ≤ ‖1 - a * x ^ k‖) :
-- imply
  (∀ k : ℕ, 1 ≤ k → 1 - r * x ^ (k - 1) ≠ 0) ∧
    Summable (chapter6Entry16LeftTerm a r x) ∧
    Summable (chapter6Entry16MiddleTerm a r x) ∧
    Summable (chapter6Entry16RightTerm a r x) ∧
    ∑' j : ℕ, chapter6Entry16LeftTerm a r x j =
      ∑' j : ℕ, chapter6Entry16MiddleTerm a r x j +
        ∑' j : ℕ, chapter6Entry16RightTerm a r x j := by
-- proof
  apply Ramanujan.Part1Ch6.Entry16InfiniteSum.ramanujan_part1_ch6_entry16_infinite_sum a r x hr hx hboundary hpoles hboundarySeparated

-- created on 2026-10-10
