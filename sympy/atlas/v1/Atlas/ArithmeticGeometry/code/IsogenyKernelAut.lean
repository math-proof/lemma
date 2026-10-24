/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/IsogenyKernelAut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Isogenies
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
