import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[num_tilings_2_n_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ) :
-- imply
  numTilings n 2 = Nat.fib (n + 1) := by
-- proof
  -- The proof uses strong induction with the Fibonacci recurrence.
  -- Base cases: d_[0, 2] = 1 = fib(1), d_[1, 2] = 1 = fib(2)
  -- Inductive step: d_[n+2, 2] = d_[n, 2] + d_[n+1, 2] by numTilings_recurrence
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · -- n = 0
      rw [numTilings_0_2]
      rfl
    · -- n = 1
      rw [numTilings_1_2]
      rfl
    · -- n + 2: use the Fibonacci recurrence
      -- By IH: d_[n, 2] = Nat.fib (n + 1) and d_[n+1, 2] = Nat.fib (n + 2)
      have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      simp only [show n + 2 + 1 = n + 3 by ring]
      simp only [show n + 1 + 1 = n + 2 by ring] at h2
      -- By Fibonacci recurrence: Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2)
      have hfib := @Nat.fib_add_two (n + 1)
      simp only [show n + 1 + 1 = n + 2 by ring, show n + 1 + 2 = n + 3 by ring] at hfib
      rw [hfib, ← h1, ← h2]
      -- Apply the recurrence lemma
      exact numTilings_recurrence n


-- created on 2026-10-20
