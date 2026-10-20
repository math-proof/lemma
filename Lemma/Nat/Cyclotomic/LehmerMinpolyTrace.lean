import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Cyclotomic.LehmerMinpolyTrace
open MetaMathlibExt


/--
[realCyclotomicPolynomial_eq_minpoly_trace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerMinpolyTrace.lean)
-/
@[path]
private lemma realCyclotomicPolynomial_eq_minpoly_trace_eq
  [Field K] [CharZero K]
  {n : ℕ}
  {zeta : K}
-- given
  (hn : 2 < n)
  (hprim : IsPrimitiveRoot zeta n) :
-- imply
  realCyclotomicPolynomial n = minpoly ℤ (zeta + zeta⁻¹) := by
-- proof
  apply MetaMathlibExt.realCyclotomicPolynomial_eq_minpoly_trace hn hprim


-- created on 2026-10-20
