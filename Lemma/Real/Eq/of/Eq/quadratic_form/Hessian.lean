import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import sympy.Basic


@[path]
private lemma main
  {a b c x : ℝ} :
-- imply
  deriv (deriv (fun t => c + b * t + a * t ^ 2)) x = a + a := by
-- proof
  have hfun : deriv (fun t => c + b * t + a * t ^ 2) = fun y => b + (a + a) * y := by
    funext y
    have h :=
      ((hasDerivAt_const y c).add ((hasDerivAt_id y).const_mul b)).add
        ((hasDerivAt_pow 2 y).const_mul a)
    have hfun : (fun t => c + b * t + a * t ^ 2) =ᶠ[nhds y]
        (((fun _ => c) + fun t => b * t) + fun t => a * t ^ 2) := by
      filter_upwards with t
      simp
    rw [(h.congr_of_eventuallyEq hfun).deriv]
    ring_nf
  rw [hfun]
  have h := (hasDerivAt_const x b).add ((hasDerivAt_id x).const_mul (a + a))
  have hfun2 : (fun t => b + (a + a) * t) =ᶠ[nhds x]
      ((fun _ => b) + fun t => (a + a) * t) := by
    filter_upwards with t
    simp
  rw [(h.congr_of_eventuallyEq hfun2).deriv]
  ring_nf


-- created on 2026-10-11
-- updated on 2026-10-17
