import Lemma.Definitions.Def_DrinfeldCurve_CoordRing
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

noncomputable section

namespace DrinfeldCurve

variable (q : ℕ) (k : Type) [Field k]

abbrev drinfeldFunctionField : Type := FractionRing (CoordRing q k)

variable [Fact q.Prime] [Algebra (GaloisField q 2) k]

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

theorem hFunctionFieldAction_algebraMap (h : hSubgroup q) (a : CoordRing q k) :
    hFunctionFieldAction q k h (algebraMap (CoordRing q k) (drinfeldFunctionField q k) a) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (hAction q k h a) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap (hAction q k h) a

theorem hFunctionFieldAction_sl (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    hFunctionFieldAction q k ⟨_, toGL_one_mem_hSubgroup q g⟩ =
      IsFractionRing.algEquivOfAlgEquiv (slAction q k g) := by
  rw [slAction_eq_hAction]
  rfl

theorem hFunctionFieldAction_mu (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) :
    hFunctionFieldAction q k ⟨_, one_mem_hSubgroup_of_mem q ζ⟩ =
      IsFractionRing.algEquivOfAlgEquiv (muAction q k ζ) := by
  rw [muAction_eq_hAction]
  rfl

end DrinfeldCurve

end
