import Lemma.Complex.ArgExpMulI.eq.DivArg
import Lemma.Complex.ArgMul.eq.Arg.of.Gt_0
import Lemma.Complex.Pow_Inv.eq.Mul_ExpMulIDivArg
open Complex


@[main]
private lemma main
-- given
  (z : ℂ)
  (n : ℕ) :
-- imply
  arg (z ^ (n : ℂ)⁻¹) = arg z / n := by
-- proof
  if hz : z = 0 then
    if hn : n = 0 then
      subst hn
      simp [hz, inv_zero, cpow_zero, arg_one, arg_zero]
    else
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      simp [hz, zero_cpow (inv_ne_zero hn'), arg_zero]
  else
    rw [Pow_Inv.eq.Mul_ExpMulIDivArg]
    have hpos : ‖z‖ ^ (n : ℝ)⁻¹ > 0 :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _
    have hcast : (n : ℂ)⁻¹ = ↑((n : ℝ)⁻¹) := by
      simp
    rw [hcast, ← ofReal_cpow (norm_nonneg z), ArgMul.eq.Arg.of.Gt_0 hpos]
    apply ArgExpMulI.eq.DivArg


-- created on 2026-08-29
