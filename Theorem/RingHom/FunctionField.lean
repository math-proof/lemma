module

public import Theorem.MvPolynomial.CoordRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Abbrev.DrinfeldCurve_FunctionField

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace DrinfeldCurve

variable (q : ℕ) (k : Type) [Field k]


public theorem hFunctionFieldAction_algebraMap (h : hSubgroup q) (a : CoordRing q k) :
    hFunctionFieldAction q k h (algebraMap (CoordRing q k) (drinfeldFunctionField q k) a) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (hAction q k h a) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap (hAction q k h) a


public theorem hFunctionFieldAction_sl (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    hFunctionFieldAction q k ⟨_, toGL_one_mem_hSubgroup q g⟩ =
      IsFractionRing.algEquivOfAlgEquiv (slAction q k g) := by
  rw [slAction_eq_hAction]
  rfl


public theorem hFunctionFieldAction_mu (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩ =
      IsFractionRing.algEquivOfAlgEquiv (muAction q k ζ) := by
  rw [muAction_eq_hAction]
  rfl

end DrinfeldCurve

end
