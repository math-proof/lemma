import Lemma.Algebra.Sub.eq.Zero
import Lemma.Algebra.GeSubS.of.Ge
open Algebra


@[main]
private lemma nat
  {x y : ℕ}
-- given
  (h : x ≥ y) :
-- imply
  (x : ℤ) - (y : ℤ) ≥ 0 := by
-- proof
  linarith


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  x - y ≥ 0 := by
-- proof
  have := GeSubS.of.Ge h y
  rw [Sub.eq.Zero] at this
  assumption


-- created on 2025-03-15
