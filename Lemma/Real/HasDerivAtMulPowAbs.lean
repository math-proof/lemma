import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Asymptotics.Lemmas
import sympy.Basic
open Asymptotics Filter Topology


@[main]
private lemma main
  {m : ℕ}
  {x : ℝ} :
-- imply
  HasDerivAt (fun y => |y| ^ m * y) ((m + 1) * |x| ^ m) x := by
-- proof
  if hm : m = 0 then
    subst hm
    simpa using hasDerivAt_id' x
  else if hx : x = 0 then
    subst hx
    rw [hasDerivAt_iff_isLittleO, ← isLittleO_norm_left]
    have h := (isLittleO_pow_id (show 1 < m + 1 by omega) : (fun y : ℝ => y ^ (m + 1)) =o[𝓝 0] fun y => y).norm_left
    convert h using 2 with y
    all_goals first | rfl | simp [hm, pow_succ]
  else
    have h := ((hasDerivAt_abs hx).pow m).mul (hasDerivAt_id' x)
    refine h.congr_deriv ?_
    have hs : (SignType.sign x : ℝ) * x = |x| := by
      if h₀ : 0 < x then
        rw [sign_pos h₀, abs_of_pos h₀]
        simp
      else
        rw [sign_neg (lt_of_le_of_ne (not_lt.1 h₀) hx), abs_of_neg (lt_of_le_of_ne (not_lt.1 h₀) hx)]
        simp
    calc
      _ = m * (|x| ^ (m - 1) * ((SignType.sign x : ℝ) * x)) + |x| ^ m := by simp only [Pi.pow_apply]; ring
      _ = m * |x| ^ m + |x| ^ m := by rw [hs, pow_sub_one_mul hm]
      _ = _ := by ring


-- created on 2026-09-26