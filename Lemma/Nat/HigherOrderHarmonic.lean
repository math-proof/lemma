import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.HigherOrderHarmonic


/--
[higherHarmonic_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean)
-/
@[path]
private lemma higherHarmonic_zero_eq
  {r : Nat} :
-- imply
  higherHarmonic 0 r = 0 := by
-- proof
  apply higherHarmonic_zero r

/--
[higherHarmonic_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean)
-/
@[path]
private lemma higherHarmonic_succ_eq
  {n r : Nat} :
-- imply
  higherHarmonic (n + 1) r =
      higherHarmonic n r + (1 : Rat) / ((((n + 1 : Nat)) : Rat) ^ r) := by
-- proof
  apply higherHarmonic_succ n r

/--
[higherHarmonic_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean)
-/
@[path]
private lemma higherHarmonic_one_eq
  {r : Nat} :
-- imply
  higherHarmonic 1 r = 1 := by
-- proof
  apply higherHarmonic_one r

/--
[higherHarmonic_order_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean)
-/
@[path]
private lemma higherHarmonic_order_one_eq
  {n : Nat} :
-- imply
  higherHarmonic n 1 = harmonic n := by
-- proof
  apply higherHarmonic_order_one n


-- created on 2026-10-20
