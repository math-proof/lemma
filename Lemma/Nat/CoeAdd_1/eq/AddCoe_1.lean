import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.OfNat.eq.Cast
open Nat


@[main, comm]
private lemma main
  [AddMonoidWithOne α]
  {a : ℕ} :
-- imply
  (a + 1 : ℕ) = (a + 1 : α) := by
-- proof
  simp


@[main, comm]
private lemma ring
  [Semiring α]
  {a : ℕ} :
-- imply
  (a + 1 : ℕ) = (a + 1 : α) := by
-- proof
  -- apply main
  rw [OfNat.eq.Cast (α := α)]
  rw [AddCoeS.eq.CoeAdd]




-- created on 2025-05-23
-- updated on 2025-11-08
