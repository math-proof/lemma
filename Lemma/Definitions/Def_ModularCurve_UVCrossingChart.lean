import Mathlib
import Lemma.Definitions.Def_ModularCurve_UVCrossingModel

set_option autoImplicit false

universe u

namespace ModularCurve

noncomputable section

namespace UVCrossingModel

section AmbientChart

variable (W : Type u) [CommRing W]

def sAmbient : MvPowerSeries (Fin 2) W :=
  MvPowerSeries.X 0 + MvPowerSeries.X 1

theorem sAmbient_def :
    sAmbient W = MvPowerSeries.X 0 + MvPowerSeries.X 1 :=
  rfl

theorem constantCoeff_sAmbient : MvPowerSeries.constantCoeff (sAmbient W) = 0 := by
  rw [sAmbient, map_add, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_X,
    add_zero]

theorem hasSubst_sAmbient : PowerSeries.HasSubst (sAmbient W) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_sAmbient W)

end AmbientChart

variable {W : Type u} [CommRing W]

def chartHom (π : W) : PowerSeries W →+* UVCrossingModel W π :=
  (mk π).comp (PowerSeries.substAlgHom (hasSubst_sAmbient W)).toRingHom

theorem chartHom_apply (π : W) (f : PowerSeries W) :
    chartHom π f = mk π (PowerSeries.subst (sAmbient W) f) := by
  show mk π ((PowerSeries.substAlgHom (hasSubst_sAmbient W)) f) = _
  rw [PowerSeries.coe_substAlgHom]

end UVCrossingModel

end

end ModularCurve
