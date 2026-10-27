import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[roth_mul_lt_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (Q A B u v w : ℝ)
-- given
  (hQ : 1 < Q)
  (hB0 : 0 ≤ B)
  (hA : A ≤ Real.rpow Q u)
  (hB : B ≤ Real.rpow Q v)
  (huv : u + v < w) :
-- imply
  A * B < Real.rpow Q w :=
-- proof
  calc
    _ ≤ Real.rpow Q u * Real.rpow Q v :=
      mul_le_mul hA hB hB0 (Real.rpow_nonneg (zero_le_one.trans hQ.le) _)
    _ = Real.rpow Q (u + v) := (Real.rpow_add (lt_trans (by norm_num) hQ) _ _).symm
    _ < Real.rpow Q w := Real.rpow_lt_rpow_of_exponent_lt hQ huv


-- created on 2026-10-21
