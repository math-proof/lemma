import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.MedianGenocchiNumber
import Lemma.Finset.Enumerative.MedianGenocchiNumber
import Lemma.Nat.GenocchiNumber
import Def.NumberTheory.GenocchiNumber


namespace MetaMathlibExt

/--
[exp_sub_one_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiBernoulli.lean)
-/
@[path]
private lemma exp_sub_one_ne_zero : PowerSeries.exp ℚ - 1 ≠ 0 := by
  intro h0
  have hc : (PowerSeries.coeff 1) (PowerSeries.exp ℚ - 1) = 0 := by
    rw [h0]
    simp
  simp [map_sub, PowerSeries.coeff_exp] at hc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[exp_add_one_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiBernoulli.lean)
-/
@[path]
private lemma exp_add_one_ne_zero : PowerSeries.exp ℚ + 1 ≠ 0 := by
  intro h0
  have hc : PowerSeries.constantCoeff (PowerSeries.exp ℚ + 1) = 0 := by
    rw [h0]
    simp
  simp [map_add, PowerSeries.constantCoeff_exp] at hc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genocchiPowerSeries_eq_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiBernoulli.lean)
`2 * x / (exp x - 1) - 4 * x / (exp (2 * x) - 1)`, i.e. `2 • B(x) - 2 • B(2 * x)` for the
Bernoulli power series `B`. -/
@[path]
private lemma genocchiPowerSeries_eq_bernoulli :
  genocchiPowerSeries =
    2 • bernoulliPowerSeries ℚ - 2 • (PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) := by
  have hB : bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) = PowerSeries.X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hB2 : (PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * ((PowerSeries.exp ℚ) ^ 2 - 1)
      = 2 • PowerSeries.X := by
    have h := congrArg (fun x : PowerSeries ℚ => (PowerSeries.rescale 2) x) hB
    simp only [map_mul, map_sub, map_one] at h
    have hsq : (PowerSeries.exp ℚ) ^ 2 = (PowerSeries.rescale 2) (PowerSeries.exp ℚ) := by
      simpa using PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) 2
    have hX : (PowerSeries.rescale 2) (PowerSeries.X : PowerSeries ℚ) = 2 • PowerSeries.X := by
      ext n
      by_cases hn : n = 1
      · subst hn
        simp [PowerSeries.coeff_X]
      · simp [PowerSeries.coeff_X, hn]
    rw [← hsq, hX] at h
    exact h
  have hG : genocchiPowerSeries * (PowerSeries.exp ℚ + 1) = 2 * PowerSeries.X := by
    rw [genocchiPowerSeries_eq, mul_assoc, PowerSeries.inv_mul_cancel]
    · ring
    · simp [map_add, PowerSeries.constantCoeff_exp]
  apply mul_right_cancel₀ exp_add_one_ne_zero
  rw [hG]
  apply mul_right_cancel₀ exp_sub_one_ne_zero
  calc 2 * PowerSeries.X * (PowerSeries.exp ℚ - 1)
      = 2 • (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) * (PowerSeries.exp ℚ + 1)
        - 2 • ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) *
          ((PowerSeries.exp ℚ) ^ 2 - 1)) := by
        rw [hB, hB2]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring
    _ = _ := by
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genocchiNumber_eq_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiBernoulli.lean)
-/
@[path]
lemma genocchiNumber_eq_bernoulli
  (n : ℕ) :
-- imply
  genocchiNumber n = 2 * (1 - (2 : ℚ) ^ n) * bernoulli n := by
-- proof
  have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [genocchiNumber_eq, genocchiPowerSeries_eq_bernoulli, map_sub, map_nsmul, map_nsmul,
    PowerSeries.coeff_rescale]
  simp only [bernoulliPowerSeries, PowerSeries.coeff_mk, nsmul_eq_mul, Nat.cast_ofNat,
    Algebra.algebraMap_self, RingHom.id_apply]
  field_simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genocchiNumberViaBernoulli_eq_genocchiNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiBernoulli.lean)
-/
@[path]
lemma genocchiNumberViaBernoulli_eq_genocchiNumber
  {n : ℕ} :
-- imply
  genocchiNumberViaBernoulli n = genocchiNumber n :=
-- proof
  (genocchiNumber_eq_bernoulli n).symm

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-28
