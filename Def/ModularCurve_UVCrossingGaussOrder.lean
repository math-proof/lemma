import Mathlib
import Lemma.ModularCurve.UVCrossingModel

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

variable {W : Type u} [CommRing W]

def inU (a : PowerSeries W) : MvPowerSeries (Fin 2) W :=
  fun d => if d 1 = 0 then PowerSeries.coeff (d 0) a else 0

def inV (b : PowerSeries W) : MvPowerSeries (Fin 2) W :=
  fun d => if d 0 = 0 then PowerSeries.coeff (d 1) b else 0


def annulusWeight (e t : ℕ) (d : Fin 2 →₀ ℕ) : ℕ := d 0 * t + d 1 * (e - t)

def repGaussOrder (v : W → ℕ∞) (e t : ℕ) (F : MvPowerSeries (Fin 2) W) : ℕ∞ :=
  ⨅ d : Fin 2 →₀ ℕ, v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞)

def gaussOrder (v : W → ℕ∞) (π : W) (e t : ℕ) (x : UVCrossingModel W π) : ℕ∞ :=
  ⨆ F ∈ {F : MvPowerSeries (Fin 2) W | mk π F = x}, repGaussOrder v e t F

end

end ModularCurve.UVCrossingModel
