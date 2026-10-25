import Def.ModularCurve_JqCoeff
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Instance.ModularCurve_TateFormal

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve

def tateB (d : ℕ) : ℤ := (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12


def tateA4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3)

def tateA6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, tateB d

def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5


def tatePowerSeries : WeierstrassCurve (PowerSeries ℤ) := ⟨1, 0, 0, tateA4, tateA6⟩


def laurentOfInt (K : Type*) [CommRing K] : PowerSeries ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (Int.castRingHom K))


def tateLaurent (K : Type*) [CommRing K] : WeierstrassCurve (LaurentSeries K) :=
  tatePowerSeries.map (laurentOfInt K)

end ModularCurve

end
