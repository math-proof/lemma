/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part3
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Isogenies
import Structure.v1.Atlas.ArithmeticGeometry.code.IsogenyKernelAut.Part2
open WeierstrassCurve


namespace EllipticCurveIsogeny

attribute [instance] KernelAutData.field_top KernelAutData.field_bot KernelAutData.algebra_inst

namespace TranslationPullbackData

variable {φ : EllipticCurveIsogeny W₁ W₂}
    (data : φ.TranslationPullbackData)

/-- Forget the isogeny-specific structure and view a `TranslationPullbackData` as the more
generic `KernelAutData` for the underlying homomorphism. -/
def toKernelAutData : KernelAutData φ.toAddMonoidHom where
  FunctionField := data.FunctionField
  PullbackField := data.PullbackField
  field_top := data.field_top
  field_bot := data.field_bot
  algebra_inst := data.algebra_inst
  translationPullback := data.translationPullback
  eval := data.eval
  eval_ext := data.eval_ext
  eval_translationPullback := data.eval_translationPullback
  eval_algebraMap_eq_of_image_eq := fun x Q R h => by
    apply data.eval_algebraMap_eq_of_image_eq
    exact h
  eval_separates := data.eval_separates

end TranslationPullbackData
end EllipticCurveIsogeny
