import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Def.CuspForm_PeterssonOn

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm


theorem peterssonOn_def (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) :
    peterssonOn Γ k f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonOnIntegrand Γ k f g) := rfl

end CuspForm

end
