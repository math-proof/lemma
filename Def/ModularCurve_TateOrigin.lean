import Mathlib
import Instance.ModularCurve_TateFormal

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def tateOriginX (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-2 : ℤ) (1 : PowerSeries K) + HahnSeries.single (-1 : ℤ) (1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k => PowerSeries.mk fun M =>
      if M = 0 then 0 else
        (∑ e ∈ M.divisors, (e : K) * ((e.choose k : K) + (-1) ^ k * ((e + k - 1).choose k : K)))
          - (if k = 0 then 2 * ∑ e ∈ M.divisors, (e : K) else 0))

def tateOriginY (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-3 : ℤ) (-1 : PowerSeries K) + HahnSeries.single (-2 : ℤ) (-2 : PowerSeries K) +
    HahnSeries.single (-1 : ℤ) (-1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k => PowerSeries.mk fun M =>
      if M = 0 then 0 else
        (∑ e ∈ M.divisors, ((e.choose 2 : K) * (e.choose k : K)
            - ((e + 1).choose 2 : K) * ((-1) ^ k * ((e + k - 1).choose k : K))))
          + (if k = 0 then ∑ e ∈ M.divisors, (e : K) else 0))

end ModularCurve

end
