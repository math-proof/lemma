import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.RadialMajorant
open Complex


namespace Complex

/--
[wimanTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean)
-/
@[path]
lemma wimanTerm_nonneg
  {f : ℂ → ℂ}
  {r : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ wimanTerm f r n :=
-- proof
mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg r) _)

end Complex

namespace Complex

/--
[summable_wimanTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean)
-/
@[path]
lemma summable_wimanTerm
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  Summable (wimanTerm f r) := by
-- proof
  let p := cauchyPowerSeries f 0 (1 : NNReal)
  have hp : HasFPowerSeriesOnBall f p 0 ⊤ :=
    hf.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) zero_lt_one
  have hp_radius : p.radius = ⊤ := le_antisymm le_top hp.r_le
  have hs : Summable (fun n : ℕ => ‖p n (fun _ => ((|r| : ℝ) : ℂ))‖) :=
    p.summable_norm_apply (by simp [hp_radius])
  apply hs.congr
  intro n
  have hfactorial := hp.factorial_smul ((|r| : ℝ) : ℂ) n
  rw [← Nat.cast_smul_eq_nsmul ℂ] at hfactorial
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_fin, smul_eq_mul] at hfactorial
  have hcoeff : p n (fun _ => ((|r| : ℝ) : ℂ)) =
    wimanTaylorCoefficient f n * ((|r| : ℝ) : ℂ) ^ n := by
    rw [wimanTaylorCoefficient, div_mul_eq_mul_div,
      eq_div_iff (mod_cast n.factorial_ne_zero)]
    simpa only [mul_comm] using hfactorial
  rw [hcoeff, wimanTerm, norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_abs]

end Complex

namespace Complex

/--
[wimanMajorant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean)
-/
@[path]
lemma wimanMajorant_nonneg
  {f : ℂ → ℂ}
  {r : ℝ} :
-- imply
  0 ≤ wimanMajorant f r :=
-- proof
tsum_nonneg fun n => wimanTerm_nonneg f r n

end Complex

namespace Complex

/--
[wimanTerm_le_wimanMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean)
-/
@[path]
lemma wimanTerm_le_wimanMajorant
  {f : ℂ → ℂ}
  {r : ℝ}
  {n : ℕ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanTerm f r n ≤ wimanMajorant f r := by
-- proof
  rw [wimanMajorant]
  exact (summable_wimanTerm f hf r).le_tsum n fun m _ => wimanTerm_nonneg f r m
end



-- created on 2026-10-20
-- updated on 2026-10-23
