/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/KaluzaCoefficientBounds.lean -/

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Kaluza's bounds for the coefficients of a reciprocal power series

If a real formal power series `f` has strictly positive log-convex coefficients `aₙ`, then the
coefficients `bₙ` of `f⁻¹` satisfy `b₀ = a₀⁻¹ > 0` and `-aₙ / a₀² ≤ bₙ ≤ 0` for `n ≥ 1`.

Source: László Tóth, *Alternating Sums Concerning Multiplicative Arithmetic Functions*,
Journal of Integer Sequences 20, Lemma `lemma_Kaluza`,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Toth/toth25.tex>. Tóth attributes the
nonpositivity of `bₙ` to T. Kaluza, Satz 3.
-/

namespace MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted

/-- Positive log-convex coefficients hypothesis for Kaluza's inverse-coefficient
bounds: every coefficient of `f` is strictly positive and
`(coeff (n+1) f)^2 ≤ coeff n f * coeff (n+2) f` for every `n`.
Source: László Tóth, *Alternating Sums Concerning Multiplicative Arithmetic
Functions*, Journal of Integer Sequences 20, Lemma `lemma_Kaluza`,
`https://cs.uwaterloo.ca/journals/JIS/VOL20/Toth/toth25.tex`, lines 553–562, file sha256
`e225aae50ee869db4df08f1a24bf6448ea544ca356369d5a0c4c7321d92607d8`, span sha256
`2ad887082f5786fc8ff64b75c3a7ddb63bc0a456290eee9cb6a85acf3c868d0f`. -/
def HasPositiveLogConvexCoefficients (f : PowerSeries ℝ) : Prop :=
  0 < PowerSeries.coeff 0 f ∧
    ∀ n : ℕ, 0 < PowerSeries.coeff (n + 1) f ∧
      (PowerSeries.coeff (n + 1) f) ^ 2 ≤
        PowerSeries.coeff n f * PowerSeries.coeff (n + 2) f
end MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted
