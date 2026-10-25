import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Def.CuspForm_Petersson

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm

variable {N : ℕ} {k : ℤ}


theorem petersson_def (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    petersson f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonIntegrand f g) := rfl

end CuspForm

end
