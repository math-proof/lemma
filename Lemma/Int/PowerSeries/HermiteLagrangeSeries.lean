import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PowerSeries.HermiteLagrangeSeries
open MetaMathlibExt


/--
[hermite_lagrange_inversion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeSeries.lean)
-/
@[path]
private lemma hermite_lagrange_inversion_eq
  {φ g F ψ : PowerSeries ℂ}
-- given
  (hφ : PowerSeries.coeff 0 φ ≠ 0)
  (hF : F * φ = PowerSeries.X)
  (hpsi1 : PowerSeries.subst ψ F = PowerSeries.X)
  (hpsi2 : PowerSeries.subst F ψ = PowerSeries.X) :
-- imply
  PowerSeries.X * PowerSeries.subst ψ g =
    (PowerSeries.mk (fun n : ℕ => PowerSeries.coeff n (g * φ ^ n)) :
    PowerSeries ℂ) * ψ *
    PowerSeries.subst ψ (PowerSeries.derivative F) := by
-- proof
  apply MetaMathlibExt.hermite_lagrange_inversion φ g F ψ hφ hF hpsi1 hpsi2


-- created on 2026-10-20
