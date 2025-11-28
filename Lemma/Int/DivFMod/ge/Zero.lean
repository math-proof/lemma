import Lemma.Rat.Div.ge.Zero.of.Mul.ge.Zero
import Lemma.Int.MulFMod.ge.Zero
open Int Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (n d : ℤ) :
-- imply
  n.fmod d / (d : α) ≥ 0 := by
-- proof
  apply Div.ge.Zero.of.Mul.ge.Zero
  norm_cast
  apply MulFMod.ge.Zero


-- created on 2025-03-21
-- updated on 2025-03-23
