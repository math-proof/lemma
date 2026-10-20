/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiNumber.lean -/

import Mathlib.RingTheory.PowerSeries.Exp

namespace MetaMathlibExt

/-- Exponential generating function of the Genocchi numbers `Gₙ`:
`2 * x / (exp x + 1) = ∑ₙ Gₙ * x ^ n / n!`.

This retains the standard `2 * x / (exp x + 1)` convention stated by Chen and
used independently by Kida; the sign-changed variant consumes only even-index
terms, where the conventions agree.

Provenance:
- phrase concept `jis_term_2151ebeb03d46b7f51d94f94`
- source statements `jis_21afe12570e34775c299908d` and `jis_5d32bc9f1d45c583ec9b9547`
- Chen, JIS VOL6 (`JIS VOL6/Chen/chen50.tex`, lines 296-300, duplicated in
  `chen53.tex`): https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.html
- Kida, JIS VOL16 (`JIS VOL16/Kida/kida2.tex`):
  https://cs.uwaterloo.ca/journals/JIS/VOL16/Kida/kida2.html -/
noncomputable def genocchiPowerSeries : PowerSeries ℚ :=
  2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹

/-- Genocchi number `Gₙ`: `n!` times coefficient `n` of `genocchiPowerSeries`,
i.e. the exponential-generating-function normalization of
`2 * x / (exp x + 1) = ∑ₙ Gₙ * x ^ n / n!`.

Provenance:
- phrase concept `jis_term_2151ebeb03d46b7f51d94f94`
- source statements `jis_21afe12570e34775c299908d` and `jis_5d32bc9f1d45c583ec9b9547`
- Chen, JIS VOL6 (`JIS VOL6/Chen/chen50.tex`, lines 296-300, duplicated in
  `chen53.tex`): https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.html
- Kida, JIS VOL16 (`JIS VOL16/Kida/kida2.tex`):
  https://cs.uwaterloo.ca/journals/JIS/VOL16/Kida/kida2.html -/
noncomputable def genocchiNumber (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (PowerSeries.coeff n) genocchiPowerSeries

/-- Interface restatement of `genocchiPowerSeries`. -/
theorem genocchiPowerSeries_eq :
    genocchiPowerSeries = 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹ :=
  rfl

/-- Interface restatement of `genocchiNumber`. -/
theorem genocchiNumber_eq (n : ℕ) :
    genocchiNumber n = (n.factorial : ℚ) * (PowerSeries.coeff n) genocchiPowerSeries :=
  rfl

end MetaMathlibExt
