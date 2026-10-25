/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part3
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Isogenies
import Def.v1.Atlas.ArithmeticGeometry.code.IsogenyKernelAut
open WeierstrassCurve


namespace EllipticCurveIsogeny

attribute [instance] KernelAutData.field_top KernelAutData.field_bot KernelAutData.algebra_inst

/-- For an elliptic curve isogeny $\varphi \colon W_1 \to W_2$, a `TranslationPullbackData`
packages the function field extension data with the translation-pullback action on the function
field, together with separation and compatibility axioms. -/
structure TranslationPullbackData (φ : EllipticCurveIsogeny W₁ W₂) extends
    φ.FunctionFieldExtension where
  translationPullback : W₁.toAffine.Point → RingAut FunctionField
  eval : FunctionField → W₁.toAffine.Point → FunctionField
  eval_ext : ∀ (f g : FunctionField), (∀ Q, eval f Q = eval g Q) → f = g
  eval_translationPullback : ∀ (P : W₁.toAffine.Point) (f : FunctionField)
    (Q : W₁.toAffine.Point),
    eval ((translationPullback P) f) Q = eval f (Q + P)
  eval_algebraMap_eq_of_image_eq : ∀ (x : PullbackField) (Q R : W₁.toAffine.Point),
    φ Q = φ R → eval (algebraMap PullbackField FunctionField x) Q =
      eval (algebraMap PullbackField FunctionField x) R
  eval_separates : ∀ (Q R : W₁.toAffine.Point), Q ≠ R →
    ∃ f : FunctionField, eval f Q ≠ eval f R

end EllipticCurveIsogeny
