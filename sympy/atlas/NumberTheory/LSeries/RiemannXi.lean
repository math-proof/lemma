/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean -/

import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The Riemann xi function

This module defines the Riemann xi function in the normalization

  `ξ(s) = s * (s - 1) / 2 * Λ₀(s) + 1 / 2`,

where `Λ₀ = completedRiemannZeta₀` is Mathlib's entire completed Riemann zeta
function (the completed zeta function with its polar parts removed). The
additive constant `1 / 2` is forced algebraically by `completedRiemannZeta_eq`
together with the requirement that `ξ` agree with `s * (s - 1) / 2 * Λ(s)`
away from the poles of `Λ` at `s = 0` and `s = 1`.

## Main results

* `RiemannXi.riemannXi`: the Riemann xi function.
* `RiemannXi.differentiable_riemannXi`: `ξ` is entire.
* `RiemannXi.riemannXi_one_sub`: the functional equation `ξ(1 - s) = ξ(s)`.
* `RiemannXi.riemannXi_eq_mul_completedRiemannZeta`: away from `s = 0, 1`,
  `ξ(s) = s * (s - 1) / 2 * Λ(s)`.
* `RiemannXi.riemannXi_ne_zero_of_one_le_re`: `ξ` does not vanish on
  `1 ≤ s.re` (proved from the agreement theorem plus
  `riemannZeta_ne_zero_of_one_le_re`; the point `s = 1` is handled separately).
* `RiemannXi.re_pos_of_riemannXi_eq_zero` and
  `RiemannXi.re_lt_one_of_riemannXi_eq_zero`: every zero of `ξ` lies in the
  open critical strip `0 < s.re < 1` (the left half follows by reflecting
  through the functional equation into the nonvanishing half-plane).
* `RiemannXi.riemannXi_entire_functional_equation_and_critical_strip`: packaged
  corollary conjoining the entireness, functional equation, and critical-strip
  claims.
-/

namespace RiemannXi

/-- The Riemann xi function `ξ(s) = s * (s - 1) / 2 * Λ₀(s) + 1 / 2`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2
end RiemannXi
