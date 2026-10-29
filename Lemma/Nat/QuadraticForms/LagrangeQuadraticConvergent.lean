import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[lagrangeQuad_completedSquare](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrangeQuad_completedSquare
  (P Q R u y : ℤ) (hsol : P * u ^ 2 + Q * u * y + R * y ^ 2 = 1) :
  (2 * P * u + Q * y) ^ 2 + (4 * P * R - Q ^ 2) * y ^ 2 = 4 * P := by
  linear_combination 4 * P * hsol

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lagrangeQuad_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrangeQuad_isCoprime
  (P Q R u y : ℤ) (hsol : P * u ^ 2 + Q * u * y + R * y ^ 2 = 1) :
  IsCoprime u y := by
  refine ⟨P * u + Q * y, R * y, ?_⟩
  calc
    (P * u + Q * y) * u + R * y * y = P * u ^ 2 + Q * u * y + R * y ^ 2 := by
      ring
    _ = 1 := hsol

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lagrangeQuad_discriminantGap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrangeQuad_discriminantGap
  (P Q R : ℤ) (hD : Q ^ 2 - 4 * P * R < 0)
  (hD3 : Q ^ 2 - 4 * P * R ≠ -3) :
  4 ≤ 4 * P * R - Q ^ 2 := by
  have hpos : 0 < 4 * P * R - Q ^ 2 := by omega
  have hne1 : 4 * P * R - Q ^ 2 ≠ 1 := by
    obtain ⟨q, hq | hq⟩ := Int.even_or_odd' Q <;> rw [hq] <;> intro h
    · ring_nf at h
      omega
    · ring_nf at h
      omega
  have hne2 : 4 * P * R - Q ^ 2 ≠ 2 := by
    obtain ⟨q, hq | hq⟩ := Int.even_or_odd' Q <;> rw [hq] <;> intro h
    · ring_nf at h
      omega
    · ring_nf at h
      omega
  have hne3 : 4 * P * R - Q ^ 2 ≠ 3 := by omega
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lagrangeQuad_absLinearTerm_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrangeQuad_absLinearTerm_mul_le
  (p δ A z : ℝ) (hp : 0 < p) (hz : 0 < z) (hδ : 4 ≤ δ)
  (hcompleted : A ^ 2 + δ * z ^ 2 = 4 * p) :
  |A| * z ≤ p := by
  have hcompleted_mul : A ^ 2 * z ^ 2 + δ * z ^ 4 = 4 * p * z ^ 2 := by
    linear_combination z ^ 2 * hcompleted
  have hsquares : A ^ 2 * z ^ 2 ≤ p ^ 2 := by
    have hδnonneg : 0 ≤ δ - 4 := sub_nonneg.mpr hδ
    have hzfour : 0 ≤ z ^ 4 := by positivity
    nlinarith [sq_nonneg (p - 2 * z ^ 2), mul_nonneg hδnonneg hzfour]
  have habs : (|A| * z) ^ 2 ≤ p ^ 2 := by
    simpa [mul_pow, sq_abs] using hsquares
  exact (sq_le_sq₀ (mul_nonneg (abs_nonneg A) hz.le) hp.le).mp habs

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lagrangeQuad_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrangeQuad_error_le
  (P Q R u y : ℤ) (hP : 0 < P) (hy : 0 < y)
  (hD : Q ^ 2 - 4 * P * R < 0)
  (hD3 : Q ^ 2 - 4 * P * R ≠ -3)
  (hsol : P * u ^ 2 + Q * u * y + R * y ^ 2 = 1) :
  |-(Q : ℝ) / (2 * (P : ℝ)) - (u : ℝ) / (y : ℝ)| ≤
    1 / (2 * (y : ℝ) ^ 2) := by
  have hpReal : 0 < (P : ℝ) := by exact_mod_cast hP
  have hyReal : 0 < (y : ℝ) := by exact_mod_cast hy
  have hgapReal : (4 : ℝ) ≤ ((4 * P * R - Q ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast lagrangeQuad_discriminantGap P Q R hD hD3
  have hcompletedReal :
      (2 * (P : ℝ) * (u : ℝ) + (Q : ℝ) * (y : ℝ)) ^ 2 +
          ((4 * P * R - Q ^ 2 : ℤ) : ℝ) * (y : ℝ) ^ 2 = 4 * (P : ℝ) := by
    exact_mod_cast lagrangeQuad_completedSquare P Q R u y hsol
  have hlinear := lagrangeQuad_absLinearTerm_mul_le
    (P : ℝ) ((4 * P * R - Q ^ 2 : ℤ) : ℝ)
    (2 * (P : ℝ) * (u : ℝ) + (Q : ℝ) * (y : ℝ)) (y : ℝ)
    hpReal hyReal hgapReal hcompletedReal
  have hden : 0 < 2 * (P : ℝ) * (y : ℝ) := by positivity
  have hrewrite :
      -(Q : ℝ) / (2 * (P : ℝ)) - (u : ℝ) / (y : ℝ) =
        -(2 * (P : ℝ) * (u : ℝ) + (Q : ℝ) * (y : ℝ)) /
          (2 * (P : ℝ) * (y : ℝ)) := by
    field_simp [hpReal.ne', hyReal.ne']
    ring
  rw [hrewrite, abs_div, abs_neg, abs_of_pos hden, div_le_iff₀ hden]
  calc
    |2 * (P : ℝ) * (u : ℝ) + (Q : ℝ) * (y : ℝ)| ≤ (P : ℝ) / (y : ℝ) :=
      (le_div_iff₀ hyReal).2 hlinear
    _ = 1 / (2 * (y : ℝ) ^ 2) * (2 * (P : ℝ) * (y : ℝ)) := by
      field_simp [hyReal.ne']

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lagrangeQuad_oneDenominator_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrangeQuad_oneDenominator_lower
  (P Q R u y : ℤ) (hP : 0 < P) (hy : 0 < y)
  (hD : Q ^ 2 - 4 * P * R < 0)
  (hD3 : Q ^ 2 - 4 * P * R ≠ -3)
  (hD4 : Q ^ 2 - 4 * P * R = -4 → P ≠ 2)
  (hsol : P * u ^ 2 + Q * u * y + R * y ^ 2 = 1) (hyOne : y = 1) :
  (-(1 / 2) : ℝ) < -(Q : ℝ) / (2 * (P : ℝ)) - (u : ℝ) := by
  subst y
  have hbound := lagrangeQuad_error_le P Q R u 1 hP (by omega) hD hD3 hsol
  norm_num at hbound
  have hlower := (abs_le.mp hbound).1
  by_contra hnot
  have heq : -(Q : ℝ) / (2 * (P : ℝ)) - (u : ℝ) = -(1 / 2) := by
    linarith
  have hpReal : 0 < (P : ℝ) := by exact_mod_cast hP
  have hlinearReal : 2 * (P : ℝ) * (u : ℝ) + (Q : ℝ) = (P : ℝ) := by
    field_simp [hpReal.ne'] at heq
    linarith
  have hlinear : 2 * P * u + Q = P := by exact_mod_cast hlinearReal
  have hcompleted := lagrangeQuad_completedSquare P Q R u 1 hsol
  norm_num at hcompleted
  rw [hlinear] at hcompleted
  have hgap := lagrangeQuad_discriminantGap P Q R hD hD3
  have hPtwo : P = 2 := by nlinarith [sq_nonneg (P - 2)]
  exact (hD4 (by nlinarith [hcompleted])) hPtwo

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lagrangeQuad_legendreAss](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrangeQuad_legendreAss
  (P Q R u y : ℤ) (hP : 0 < P) (hy : 0 < y)
  (hD : Q ^ 2 - 4 * P * R < 0)
  (hD3 : Q ^ 2 - 4 * P * R ≠ -3)
  (hD4 : Q ^ 2 - 4 * P * R = -4 → P ≠ 2)
  (hsol : P * u ^ 2 + Q * u * y + R * y ^ 2 = 1) :
  Real.ContfracLegendre.Ass (-(Q : ℝ) / (2 * (P : ℝ))) u y := by
  refine ⟨lagrangeQuad_isCoprime P Q R u y hsol, ?_, ?_⟩
  · exact lagrangeQuad_oneDenominator_lower P Q R u y hP hy hD hD3 hD4 hsol
  · have hbound := lagrangeQuad_error_le P Q R u y hP hy hD hD3 hsol
    have hyReal : 0 < (y : ℝ) := by exact_mod_cast hy
    have hsmallDen : 0 < (y : ℝ) * (2 * (y : ℝ) - 1) := by
      have : 0 < 2 * (y : ℝ) - 1 := by exact_mod_cast (show 0 < 2 * y - 1 by omega)
      positivity
    have hdenLt : (y : ℝ) * (2 * (y : ℝ) - 1) < 2 * (y : ℝ) ^ 2 := by
      nlinarith
    exact hbound.trans_lt <| by
      simpa [one_div] using one_div_lt_one_div_of_lt hsmallDen hdenLt

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lagrangeQuad_exists_convergent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrangeQuad_exists_convergent
  (P Q R u y : ℤ) (hP : 0 < P) (hy : 0 < y)
  (hD : Q ^ 2 - 4 * P * R < 0)
  (hD3 : Q ^ 2 - 4 * P * R ≠ -3)
  (hD4 : Q ^ 2 - 4 * P * R = -4 → P ≠ 2)
  (hsol : P * u ^ 2 + Q * u * y + R * y ^ 2 = 1) :
  let ω : ℝ := -(Q : ℝ) / (2 * (P : ℝ))
  ∃ n : ℕ, ((ω.convergent n : ℚ) : ℝ) = (u : ℝ) / (y : ℝ) := by
  dsimp only
  have hyNatCast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy.le
  have hAss : Real.ContfracLegendre.Ass
      (-(Q : ℝ) / (2 * (P : ℝ))) u (y.toNat : ℤ) := by
    rw [hyNatCast]
    exact lagrangeQuad_legendreAss P Q R u y hP hy hD hD3 hD4 hsol
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent' hAss
  refine ⟨n, ?_⟩
  have hyNatCastReal : (y.toNat : ℝ) = (y : ℝ) := by exact_mod_cast hyNatCast
  rw [← hn, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, hyNatCastReal]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lagrange_quadratic_convergent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
lemma lagrange_quadratic_convergent
  (P Q R u y : ℤ)
-- given
  (hP : 0 < P)
  (hy : 0 < y)
  (hD : Q ^ 2 - 4 * P * R < 0)
  (hD3 : Q ^ 2 - 4 * P * R ≠ -3)
  (hD4 : Q ^ 2 - 4 * P * R = -4 → P ≠ 2)
  (hsol : P * u ^ 2 + Q * u * y + R * y ^ 2 = 1) :
  let ω : ℝ := -(Q : ℝ) / (2 * (P : ℝ))
  ∃ n : ℕ,
    (n = 0 ∨ ¬(GenContFract.of ω).TerminatedAt (n - 1)) ∧
      ((ω.convergent n : ℚ) : ℝ) = (u : ℝ) / (y : ℝ) := by
  classical
  let ω : ℝ := -(Q : ℝ) / (2 * (P : ℝ))
  change ∃ n : ℕ,
    (n = 0 ∨ ¬(GenContFract.of ω).TerminatedAt (n - 1)) ∧
      ((ω.convergent n : ℚ) : ℝ) = (u : ℝ) / (y : ℝ)
  have hexists : ∃ n : ℕ,
      ((ω.convergent n : ℚ) : ℝ) = (u : ℝ) / (y : ℝ) := by
    simpa [ω] using lagrangeQuad_exists_convergent P Q R u y hP hy hD hD3 hD4 hsol
  let n := Nat.find hexists
  have hnSpec : ((ω.convergent n : ℚ) : ℝ) = (u : ℝ) / (y : ℝ) := by
    simpa [n] using Nat.find_spec hexists
  refine ⟨n, ?_, hnSpec⟩
  by_cases hnZero : n = 0
  · exact Or.inl hnZero
  · refine Or.inr fun hterminated => ?_
    have hstable :
        ((ω.convergent n : ℚ) : ℝ) = ((ω.convergent (n - 1) : ℚ) : ℝ) := by
      calc
        ((ω.convergent n : ℚ) : ℝ) = (GenContFract.of ω).convs n :=
          (Real.convs_eq_convergent ω n).symm
        _ = (GenContFract.of ω).convs (n - 1) :=
          GenContFract.convs_stable_of_terminated (Nat.sub_le n 1) hterminated
        _ = ((ω.convergent (n - 1) : ℚ) : ℝ) :=
          Real.convs_eq_convergent ω (n - 1)
    have hprevious :
        ((ω.convergent (n - 1) : ℚ) : ℝ) = (u : ℝ) / (y : ℝ) :=
      hstable.symm.trans hnSpec
    have hlt : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hnZero) Nat.one_pos
    exact (Nat.find_min hexists (by simpa [n] using hlt)) hprevious

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-28
