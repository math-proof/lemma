/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part3
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Isogenies
import Structure.v1.Atlas.ArithmeticGeometry.code.IsogenyKernelAut
open WeierstrassCurve


namespace EllipticCurveIsogeny

attribute [instance] KernelAutData.field_top KernelAutData.field_bot KernelAutData.algebra_inst

/-- Translation pullback restricted to $\ker\varphi_{\mathrm{hom}}$, viewed as an additive
homomorphism into `Additive (RingAut FunctionField)`. -/
def translationPullbackHomOnKer :
    φ_hom.ker →+ Additive (RingAut data.FunctionField) where
  toFun P := Additive.ofMul (data.translationPullback P.val)
  map_zero' := by
    simp only [AddSubgroup.coe_zero]
    exact congrArg Additive.ofMul data.translationPullback_zero
  map_add' P Q := by
    simp only [AddSubgroup.coe_add]
    exact congrArg Additive.ofMul (data.translation_comp_pullback P.val Q.val)

end EllipticCurveIsogeny
