import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.HigherOrderHarmonic


/--
[higherHarmonic_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean)
-/
@[path]
lemma higherHarmonic_zero
  {r : Nat} :
-- imply
  higherHarmonic 0 r = 0 := by
-- proof
  unfold higherHarmonic
  simp

/--
[higherHarmonic_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean)
-/
@[path]
lemma higherHarmonic_succ
  {n r : Nat} :
-- imply
  higherHarmonic (n + 1) r =
      higherHarmonic n r + (1 : Rat) / ((((n + 1 : Nat)) : Rat) ^ r) := by
-- proof
  unfold higherHarmonic
  rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]

/--
[higherHarmonic_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean)
-/
@[path]
lemma higherHarmonic_one
  {r : Nat} :
-- imply
  higherHarmonic 1 r = 1 := by
-- proof
  unfold higherHarmonic
  rw [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_pow, div_one]

/--
[higherHarmonic_order_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HigherOrderHarmonic.lean)
-/
@[path]
lemma higherHarmonic_order_one
  {n : Nat} :
-- imply
  higherHarmonic n 1 = harmonic n := by
-- proof
  induction n with
  | zero => simp [higherHarmonic, harmonic]
  | succ n ih =>
    rw [higherHarmonic_succ, ih, harmonic_succ, pow_one, one_div]


-- created on 2026-10-20
-- updated on 2026-10-26
