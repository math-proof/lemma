import sympy.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Interval.Finset.SuccPred


private lemma insert_Ico (a : ℤ) (n : ℕ) :
  insert (a + n) (Finset.Ico a (a + n)) = Finset.Ico a (a + n + 1) := by
  have h : a ≤ a + n := by omega
  simpa [Nat.cast_add, add_assoc] using Finset.insert_Ico_right_eq_Ico_add_one (a := a) (b := a + n) h


@[main]
private lemma main
-- given
  (a : ℤ)
  (n : ℕ) :
-- imply
  (Finset.range n).map (Nat.castEmbedding.trans (addLeftEmbedding a)) = Finset.Ico a (a + n) := by
-- proof
  induction n with
  | zero =>
    simp [Nat.castEmbedding, addLeftEmbedding]
  | succ n ih =>
    simp [Finset.range_add_one, Finset.map_insert]
    rw [ih]
    simpa [Nat.cast_add, add_assoc] using insert_Ico a n


-- created on 2018-04-24
