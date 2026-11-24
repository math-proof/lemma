module
public import Lemma.MvPolynomial.CoordRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Abbrev.DrinfeldCurve_FunctionField
set_option autoImplicit false


public section

noncomputable section

namespace DrinfeldCurve

variable (q : ℕ) (k : Type) [Field k]

def hFunctionFieldAction : hSubgroup q →* (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) where
  toFun h := IsFractionRing.algEquivOfAlgEquiv (hAction q k h)
  map_one' := by
    apply AlgEquiv.ext
    intro x
    have key : ((IsFractionRing.algEquivOfAlgEquiv (hAction q k 1) :
          drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
            drinfeldFunctionField q k →+* drinfeldFunctionField q k) = RingHom.id _ := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k))
      ext a
      simp [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    simpa using RingHom.congr_fun key x
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    have key : ((IsFractionRing.algEquivOfAlgEquiv (hAction q k (g * h)) :
          drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
            drinfeldFunctionField q k →+* drinfeldFunctionField q k) =
        ((IsFractionRing.algEquivOfAlgEquiv (hAction q k g) :
          drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
            drinfeldFunctionField q k →+* drinfeldFunctionField q k).comp
          ((IsFractionRing.algEquivOfAlgEquiv (hAction q k h) :
            drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
              drinfeldFunctionField q k →+* drinfeldFunctionField q k) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k))
      ext a
      simp [IsFractionRing.algEquivOfAlgEquiv_algebraMap, map_mul]
    simpa using RingHom.congr_fun key x

end DrinfeldCurve

end
