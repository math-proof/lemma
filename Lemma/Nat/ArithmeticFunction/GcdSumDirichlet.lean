import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.GcdSumDirichlet
open MetaMathlibExt


/--
[dirichlet_series_gcd_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/GcdSumDirichlet.lean)
-/
@[path]
private lemma dirichlet_series_gcd_sum_eq
  {s : ℂ}
-- given
  (hs : 2 < s.re) :
-- imply
  (∑' n : ℕ, ((∑ i ∈ Finset.range (n + 1), (Nat.gcd (n + 1) (i + 1) : ℂ))
    / (((n + 1 : ℕ) : ℂ)) ^ s))
    = riemannZeta (s - 1) ^ 2 / riemannZeta s := by
-- proof
  apply MetaMathlibExt.dirichlet_series_gcd_sum s hs


-- created on 2026-10-20
