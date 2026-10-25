import Mathlib

set_option autoImplicit false

open MeasureTheory.Measure
open scoped NNReal


namespace FLT.HaarFiniteOrderGates

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

section Inversion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

@[to_additive

                                                   ]
def invContinuousMulEquiv : G ≃ₜ* G where
  toFun g := g⁻¹
  invFun g := g⁻¹
  left_inv g := inv_inv g
  right_inv g := inv_inv g
  map_mul' a b := mul_inv a b
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv

end Inversion


section Separation

noncomputable def doublingContinuousAddEquiv : ℝ ≃ₜ+ ℝ where
  toFun x := 2 * x
  invFun x := 2⁻¹ * x
  left_inv x := by norm_num [← mul_assoc]
  right_inv x := by norm_num [← mul_assoc]
  map_add' a b := mul_add 2 a b
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Separation

end FLT.HaarFiniteOrderGates
