import Lemma.Algebra.Div.ge.Zero.of.Mul.ge.Zero
import Lemma.Int.MulFMod.ge.Zero
open Algebra Int


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n.fmod d / (d : ℚ) ≥ 0 := by
-- proof
  apply Div.ge.Zero.of.Mul.ge.Zero
  norm_cast
  apply MulFMod.ge.Zero


-- created on 2025-03-21
-- updated on 2025-03-23
