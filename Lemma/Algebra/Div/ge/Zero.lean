import Lemma.Algebra.Div.ge.Zero.of.Ge_0.Ge_0
import Lemma.Int.Ge_0
open Algebra Int


@[main]
private lemma main
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {a b : ℕ} :
-- imply
  (a : R) / (b : R) ≥ 0 := by
-- proof
  apply Div.ge.Zero.of.Ge_0.Ge_0 <;>
    apply Ge_0


-- created on 2025-07-06
