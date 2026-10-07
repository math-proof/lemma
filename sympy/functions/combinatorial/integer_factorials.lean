import sympy.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
SymPy's `RisingFactorial(x, k)` for integer `k` (`rf(x, -k) = 1 / rf(x - k, k)`), and `binomial(n, k)`
for integer `k` (zero for negative `k`). For natural `k`, `RisingFactorial x k` is
`(ascPochhammer R k).eval x`, which is what lemmas with a natural index use directly.
-/

noncomputable def RisingFactorial {R : Type*} [Field R] (x : R) (k : ℤ) : R :=
  if 0 ≤ k then (ascPochhammer R k.toNat).eval x else 1 / (ascPochhammer R (-k).toNat).eval (x + k)

def Binomial (n : ℕ) (k : ℤ) : ℤ :=
  if 0 ≤ k then (n.choose k.toNat : ℤ) else 0


noncomputable def FallingFactorial {R : Type*} [Field R] (x : R) (k : ℤ) : R :=
  if 0 ≤ k then (descPochhammer R k.toNat).eval x else 1 / (descPochhammer R (-k).toNat).eval (x - k)

