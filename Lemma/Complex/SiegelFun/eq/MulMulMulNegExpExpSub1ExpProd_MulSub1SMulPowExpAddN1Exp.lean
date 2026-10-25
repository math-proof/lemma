import Mathlib
import sympy.Basic
import Lemma.ModularCurve.SiegelFunction
open ModularCurve


/--
[siegelFun_def](Lemma/Definitions/Def_ModularCurve_SiegelFunction.lean)
-/
@[path]
private lemma main
  {N : ℕ}
  {r s : ℤ}
  {z : ℂ} :
-- imply
  siegelFun N r s z =
    -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
      Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
      (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
      (tprod fun n : ℕ =>
        (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
          Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
          (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹)) := by
-- proof
  apply siegelFun_def


-- created on 2026-10-24
