import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm

variable {N : ℕ} {k : ℤ}

def peterssonIntegrand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    UpperHalfPlane.petersson k (⇑f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (⇑g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

def petersson (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd) (peterssonIntegrand f g)

end CuspForm

end
