import Lemma.Algebra.Div.ge.Zero.of.Ge_0.Ge_0
import Lemma.Algebra.Ge_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField R]
  {a b : ℕ} :
-- imply
  (a : R) / (b : R) ≥ 0 := by
-- proof
  apply Div.ge.Zero.of.Ge_0.Ge_0 <;>
    apply Ge_0


-- created on 2025-07-06
