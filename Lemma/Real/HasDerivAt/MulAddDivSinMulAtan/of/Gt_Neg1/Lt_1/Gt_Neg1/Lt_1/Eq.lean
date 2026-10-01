import Lemma.Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import sympy.Basic


/--
Antiderivative of the squared polar radius \(r^2/2=\dfrac{p^2}{2(1-e\cos x)^2}\).
Write \(e=\dfrac{2q}{1+q^2}\) (with \(|q|<1\)); then
\[
\frac{d}{dx}\left[\frac{p^2}{2(1-e^2)}\left(\frac{e\sin x}{1-e\cos x}
+\frac{1+q^2}{1-q^2}\Big(x+2\arctan\frac{q\sin x}{1-q\cos x}\Big)\right)\right]
=\frac12\left(\frac{p}{1-e\cos x}\right)^2.
\]
-/
@[main]
private lemma main
  {e q p : ℝ}
-- given
  (he₀ : -1 < e)
  (he₁ : e < 1)
  (hq₀ : -1 < q)
  (hq₁ : q < 1)
  (hrel : e * (1 + q ^ 2) = 2 * q)
  (x : ℝ) :
-- imply
  HasDerivAt
    (fun x =>
      p ^ 2 / 2 * (1 / (1 - e ^ 2)) *
        (e * (Real.sin x / (1 - e * Real.cos x)) +
          (1 + q ^ 2) / (1 - q ^ 2) * (x + 2 * Real.arctan (q * Real.sin x / (1 - q * Real.cos x)))))
    ((p / (1 - e * Real.cos x)) ^ 2 / 2) x := by
-- proof
  have hsc := Real.sin_sq_add_cos_sq x
  have hD : 1 - e * Real.cos x ≠ 0 :=
    (Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1 he₀ he₁ x).ne'
  have hDq : 1 - q * Real.cos x ≠ 0 :=
    (Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1 hq₀ hq₁ x).ne'
  have h1e : 1 - e ^ 2 ≠ 0 := by nlinarith
  have hq2 : 1 - q ^ 2 ≠ 0 := by nlinarith
  have hq2' : 1 + q ^ 2 ≠ 0 := by positivity
  have hN : 1 - 2 * q * Real.cos x + q ^ 2 = (1 + q ^ 2) * (1 - e * Real.cos x) := by
    linear_combination (Real.cos x) * hrel
  have hNne : 1 - 2 * q * Real.cos x + q ^ 2 ≠ 0 := by
    rw [hN]
    exact mul_ne_zero hq2' hD
  -- derivative of sin x / (1 - e cos x)
  have hDd : HasDerivAt (fun x => 1 - e * Real.cos x) (e * Real.sin x) x := by
    simpa using ((Real.hasDerivAt_cos x).const_mul e).const_sub 1
  have h₁ := (Real.hasDerivAt_sin x).div hDd hD
  -- derivative of x + 2 arctan (q sin x / (1 - q cos x))
  have hDqd : HasDerivAt (fun x => 1 - q * Real.cos x) (q * Real.sin x) x := by
    simpa using ((Real.hasDerivAt_cos x).const_mul q).const_sub 1
  have hu := ((Real.hasDerivAt_sin x).const_mul q).div hDqd hDq
  have h₂ := (hasDerivAt_id x).add (hu.arctan.const_mul 2)
  have h := ((h₁.const_mul e).add (h₂.const_mul ((1 + q ^ 2) / (1 - q ^ 2)))).const_mul
    (p ^ 2 / 2 * (1 / (1 - e ^ 2)))
  refine h.congr_deriv ?_
  simp only [Pi.div_apply]
  have hs : (1 - q * Real.cos x) ^ 2 + (q * Real.sin x) ^ 2 = 1 - 2 * q * Real.cos x + q ^ 2 := by
    linear_combination q ^ 2 * hsc
  have h3 : 1 + (q * Real.sin x / (1 - q * Real.cos x)) ^ 2 =
      (1 - 2 * q * Real.cos x + q ^ 2) / (1 - q * Real.cos x) ^ 2 := by
    rw [← hs]
    field_simp
  have hDq' : 1 - Real.cos x * q ≠ 0 := by rwa [mul_comm]
  have hs2 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by linarith
  have he : e = 2 * q / (1 + q ^ 2) := by field_simp; linarith
  rw [h3, hN]
  subst he
  have hDe : 1 - 2 * q / (1 + q ^ 2) * Real.cos x ≠ 0 := hD
  have hN1 : 1 + q ^ 2 - 2 * q * Real.cos x ≠ 0 := by intro h0; apply hNne; linarith
  have hN2 : (1 + q ^ 2) ^ 2 - 2 ^ 2 * q ^ 2 ≠ 0 := by
    have : (1 + q ^ 2) ^ 2 - 2 ^ 2 * q ^ 2 = (1 - q ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_ne_zero 2 hq2
  field_simp at hDe ⊢
  rw [hs2]
  field_simp
  ring


-- created on 2026-09-29