/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean -/

-- Author: @toskua, Avocado

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The entire exponential integral

This file defines

`Ein z = sum_(j >= 1) (-1)^(j+1) z^j / (j * j!)`

and proves its elementary analytic and derivative properties.
-/

namespace Complex

noncomputable section

open Set

/-- The `j = n + 1` term of the entire power series for `Ein`. -/
def einTerm (n : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * z ^ (n + 1) /
    (((n + 1 : ℕ) : ℂ) * ((n + 1).factorial : ℂ))

/-- The entire exponential integral
`Ein z = sum_(j >= 1) (-1)^(j+1) z^j / (j * j!)`. -/
def ein (z : ℂ) : ℂ :=
  ∑' n : ℕ, einTerm n z
end
