import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import sympy.Basic


@[path]
private lemma main
  {a b c x : ℝ} :
-- imply
  deriv (fun t => c + b * t + a * t ^ 2) x = (a + a) * x + b := by
-- proof
  have h :=
    ((hasDerivAt_const x c).add ((hasDerivAt_id x).const_mul b)).add
      ((hasDerivAt_pow 2 x).const_mul a)
  have hfun : (fun t => c + b * t + a * t ^ 2) =
      ((fun _ => c) + fun y => b * id y) + fun y => a * y ^ 2 := by
    funext t
    simp [id]
  rw [hfun, h.deriv]
  ring_nf


-- created on 2021-12-25
-- updated on 2026-10-17
