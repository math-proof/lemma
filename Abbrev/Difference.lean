import Mathlib.Algebra.Group.ForwardDiff

/-- sympy `Difference(f(x), (x, n))`: the `n`-th forward difference with unit step, realized by Mathlib's `fwdDiff 1` iterated `n` times. -/
abbrev Difference {M G : Type*} [AddCommMonoid M] [One M] [AddCommGroup G] (f : M → G) (n : ℕ) : M → G :=
  (fwdDiff (1 : M))^[n] f
