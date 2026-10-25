import Mathlib
import Lemma.ModularCurve.UVCrossingModel
import Def.ModularCurve_UVCrossingGaussOrder

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

variable {W : Type u} [CommRing W]


theorem coeff_inU (a : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inU a) = if d 1 = 0 then PowerSeries.coeff (d 0) a else 0 := rfl

theorem coeff_inV (b : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inV b) = if d 0 = 0 then PowerSeries.coeff (d 1) b else 0 := rfl


theorem repGaussOrder_le (v : W → ℕ∞) (e t : ℕ) (F : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    repGaussOrder v e t F ≤ v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) :=
  iInf_le _ d

theorem le_repGaussOrder_iff (v : W → ℕ∞) (e t : ℕ) (F : MvPowerSeries (Fin 2) W) (n : ℕ∞) :
    n ≤ repGaussOrder v e t F ↔ ∀ d, n ≤ v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) :=
  le_iInf_iff

theorem repGaussOrder_le_gaussOrder (v : W → ℕ∞) (π : W) (e t : ℕ) (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder v e t F ≤ gaussOrder v π e t (mk π F) :=
  le_iSup₂ (f := fun G (_ : G ∈ {G : MvPowerSeries (Fin 2) W | mk π G = mk π F}) => repGaussOrder v e t G) F rfl

theorem gaussOrder_le_iff (v : W → ℕ∞) (π : W) (e t : ℕ) (x : UVCrossingModel W π) (n : ℕ∞) :
    gaussOrder v π e t x ≤ n ↔ ∀ F, mk π F = x → repGaussOrder v e t F ≤ n :=
  iSup₂_le_iff

end

end ModularCurve.UVCrossingModel
