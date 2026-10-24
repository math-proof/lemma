/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/RiemannXi.lean -/


import sympy.atlas.NumberTheory.LSeries.RiemannXi
import Lemma.Nat.LSeries.RiemannXi


/-!
# Tests for the Riemann xi function

Focused elaboration/API checks: the defining equation, entireness, the
functional equation, agreement with the completed zeta function away from
`s = 0, 1`, nonvanishing on `1 ≤ s.re`, the critical-strip location of zeros,
and the packaged corollary.
-/

namespace RiemannXiTest

/-- The definition unfolds to the stated normalization. -/
example (s : ℂ) :
    RiemannXi.riemannXi s =
      s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2 :=
  rfl

/-- Entireness API. -/
example : Differentiable ℂ RiemannXi.riemannXi :=
  RiemannXi.differentiable_riemannXi

/-- Functional-equation API. -/
example (s : ℂ) : RiemannXi.riemannXi (1 - s) = RiemannXi.riemannXi s :=
  RiemannXi.riemannXi_one_sub s

/-- Agreement with the completed zeta function away from `s = 0, 1`. -/
example {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    RiemannXi.riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s :=
  RiemannXi.riemannXi_eq_mul_completedRiemannZeta hs0 hs1

/-- Nonvanishing on the closed half-plane `1 ≤ s.re`. -/
example {s : ℂ} (hs : 1 ≤ s.re) : RiemannXi.riemannXi s ≠ 0 :=
  RiemannXi.riemannXi_ne_zero_of_one_le_re hs

/-- Zeros have strictly positive real part. -/
example {s : ℂ} (h : RiemannXi.riemannXi s = 0) : 0 < s.re :=
  RiemannXi.re_pos_of_riemannXi_eq_zero h

/-- Zeros have real part strictly less than one. -/
example {s : ℂ} (h : RiemannXi.riemannXi s = 0) : s.re < 1 :=
  RiemannXi.re_lt_one_of_riemannXi_eq_zero h

/-- Zeros lie in the open critical strip. -/
example {s : ℂ} (h : RiemannXi.riemannXi s = 0) : 0 < s.re ∧ s.re < 1 :=
  RiemannXi.riemannXi_mem_strip h

/-- The packaged corollary is available. -/
example :
    Differentiable ℂ RiemannXi.riemannXi ∧
      (∀ s : ℂ, RiemannXi.riemannXi (1 - s) = RiemannXi.riemannXi s) ∧
      ∀ s : ℂ, RiemannXi.riemannXi s = 0 → 0 < s.re ∧ s.re < 1 :=
  RiemannXi.riemannXi_entire_functional_equation_and_critical_strip

end RiemannXiTest
