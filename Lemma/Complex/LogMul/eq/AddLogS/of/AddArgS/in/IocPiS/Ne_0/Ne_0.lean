import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  {x y : ℂ}
-- given
  (hx₀ : x ≠ 0)
  (hy₀ : y ≠ 0)
  (h : x.arg + y.arg ∈ Ioc (-Real.pi) Real.pi) :
-- imply
  (x * y).log = x.log + y.log :=
-- proof
  Complex.log_mul hx₀ hy₀ h


-- created on 2025-12-03
