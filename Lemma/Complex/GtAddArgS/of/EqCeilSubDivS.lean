import sympy.core.numbers
import sympy.functions.elementary.complexes
import Lemma.Algebra.Gt_0.of.Eq
import Lemma.Int.Gt_0.of.Lt0Ceil
open Algebra Int


@[main]
private lemma main
  {A B : ℂ}
-- given
  (h : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 1) :
-- imply
  arg A + arg B > π := by
-- proof
  have h_ceil : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ > 0 := by
    rw [h]
    norm_num
  have h_pos : (arg A + arg B) / (2 * π) - 1 / 2 > 0 :=
    Gt_0.of.Lt0Ceil h_ceil
  have hπ : 0 < 2 * π := mul_pos two_pos Real.pi_pos
  have h_div : 1 / 2 < (arg A + arg B) / (2 * π) := sub_pos.mp h_pos
  have := (lt_div_iff₀ hπ).mp h_div
  linarith


-- created on 2018-10-31
-- updated on 2026-08-20
