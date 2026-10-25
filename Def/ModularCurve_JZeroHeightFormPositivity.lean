import Lemma.ModularCurve.JZeroHeightForm
import Instance.Compat_Mathlib430

set_option autoImplicit false
set_option Elab.async false

open ModularCurve AlgebraicCurve

namespace ModularCurve.JZero

noncomputable def offBaseMass (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℤ :=
  (D.erase (cuspInftyBar N)).sum fun _ m => m

noncomputable def baseMass (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  (D.erase (cuspInftyBar N)).sum fun v m => (m : ℝ) * baseHt s (cuspInftyBar N) v

noncomputable def heightPairing (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  baseHt s (cuspInftyBar N) v + baseHt s (cuspInftyBar N) w - pairHt s v w

end ModularCurve.JZero
