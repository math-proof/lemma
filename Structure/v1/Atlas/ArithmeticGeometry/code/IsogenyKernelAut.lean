/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Isogenies.Part3
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Isogenies
open WeierstrassCurve


namespace EllipticCurveIsogeny

/-- Auxiliary data witnessing Lemma 24.4 at the level of a generic homomorphism
$\varphi_{\mathrm{hom}} \colon E_1 \to E_2$: a function field and a smaller "pullback" field
related by translation pullback maps, with separation and compatibility axioms. -/
structure KernelAutData {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ_hom : W₁.toAffine.Point →+ W₂.toAffine.Point) where
  FunctionField : Type
  PullbackField : Type
  [field_top : Field FunctionField]
  [field_bot : Field PullbackField]
  [algebra_inst : Algebra PullbackField FunctionField]
  translationPullback : W₁.toAffine.Point → RingAut FunctionField
  eval : FunctionField → W₁.toAffine.Point → FunctionField
  eval_ext : ∀ (f g : FunctionField), (∀ Q, eval f Q = eval g Q) → f = g
  eval_translationPullback : ∀ (P : W₁.toAffine.Point) (f : FunctionField)
    (Q : W₁.toAffine.Point),
    eval ((translationPullback P) f) Q = eval f (Q + P)
  eval_algebraMap_eq_of_image_eq : ∀ (x : PullbackField) (Q R : W₁.toAffine.Point),
    φ_hom Q = φ_hom R → eval (algebraMap PullbackField FunctionField x) Q =
      eval (algebraMap PullbackField FunctionField x) R
  eval_separates : ∀ (Q R : W₁.toAffine.Point), Q ≠ R →
    ∃ f : FunctionField, eval f Q ≠ eval f R

end EllipticCurveIsogeny
