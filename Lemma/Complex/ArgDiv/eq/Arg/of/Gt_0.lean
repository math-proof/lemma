import Lemma.Complex.ArgMul.eq.Arg.of.Gt_0
open Complex


@[main]
private lemma main
  {z : ℂ}
  {r : ℝ}
-- given
  (h : r > 0) :
-- imply
  arg (z / ↑r) = arg z := by
-- proof
  rw [div_eq_mul_inv, ← ofReal_inv, mul_comm]
  exact ArgMul.eq.Arg.of.Gt_0 (inv_pos.mpr h)


-- created on 2026-08-31
