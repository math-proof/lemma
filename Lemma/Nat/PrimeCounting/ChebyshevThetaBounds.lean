import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.ChebyshevThetaBounds
open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log id
open MetaMathlibExt


/--
[chebyshev_theta_explicit_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ChebyshevThetaBounds.lean)
-/
@[path]
private lemma chebyshev_theta_explicit_bounds_eq
  {x : ℝ}
-- given
  (hx : 1 < x) :
-- imply
  let A : ℝ := by
-- proof
  apply MetaMathlibExt.chebyshev_theta_explicit_bounds x hx


-- created on 2026-10-20
