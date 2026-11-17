module

public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Def.CuspForm_Petersson

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm

variable {N : ℕ} {k : ℤ}


public theorem petersson_def (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    petersson f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonIntegrand f g) := rfl

end CuspForm

end
