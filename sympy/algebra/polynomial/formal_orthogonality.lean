
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Module.LinearMap.Basic

namespace MetaMathlibExt.Polynomial


/-- Formal orthogonality of a polynomial family over a field: `p` is
formally orthogonal iff there is a linear functional `L` on polynomials
with `(p n).natDegree = n` for all `n`, `L (p n * p m) = 0` for `n ≠ m`,
and `L (p n ^ 2) ≠ 0` for all `n`.
Source: Barry, JIS VOL14 (`Barry1/barry97r2.tex`), lines 326-331.
URL: https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry1/barry97r2.tex
Source SHA-256:
390bd7d75055d92085e8cd502df8b435fc1e45b1bbf8920038605d3fa1d1fe80
Span SHA-256 (lines 326-331):
b07808c63afc70c48dba4ed787a9177647fe9407b297ab37164f8350bbfbc8d6 -/
def IsFormallyOrthogonal {R : Type*} [Field R]
    (p : ℕ → Polynomial R) : Prop :=
  ∃ L : Polynomial R →ₗ[R] R, (∀ n, (p n).natDegree = n) ∧
    (∀ n m, n ≠ m → L (p n * p m) = 0) ∧ ∀ n, L (p n ^ 2) ≠ 0


end MetaMathlibExt.Polynomial
