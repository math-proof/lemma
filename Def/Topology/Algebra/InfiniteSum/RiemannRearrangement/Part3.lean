import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorem.Topology.Algebra.InfiniteSum.RiemannRearrangement.Part2


namespace Series.RiemannRearrangementWanted

open BigOperators

/-- One greedy step: take the next fresh nonnegative index if the partial sum is at
most `a`, otherwise the next fresh negative index. -/
noncomputable def greedyStep (f : ℕ → ℝ) (a : ℝ) (t : ℕ × ℕ × ℝ) : ℕ × ℕ × ℝ :=
  if t.2.2 ≤ a then (t.1 + 1, t.2.1, t.2.2 + f (posEnum f t.1))
  else (t.1, t.2.1 + 1, t.2.2 + f (negEnum f t.2.1))

/-- Greedy state after `n` steps: consumed nonnegative count, consumed negative
count, and current partial sum. -/
noncomputable def greedyState (f : ℕ → ℝ) (a : ℝ) : ℕ → ℕ × ℕ × ℝ
  | 0 => (0, 0, 0)
  | n + 1 => greedyStep f a (greedyState f a n)

/-- Number of nonnegative indices consumed after `n` steps. -/
noncomputable def greedyPi (f : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℕ :=
  (greedyState f a n).1

/-- Number of negative indices consumed after `n` steps. -/
noncomputable def greedyQj (f : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℕ :=
  (greedyState f a n).2.1

/-- Greedy partial sum after `n` steps. -/
noncomputable def greedySum (f : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℝ :=
  (greedyState f a n).2.2

/-- Index chosen at step `n`. -/
noncomputable def greedyIdx (f : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℕ :=
  if greedySum f a n ≤ a then posEnum f (greedyPi f a n)
  else negEnum f (greedyQj f a n)

end Series.RiemannRearrangementWanted
