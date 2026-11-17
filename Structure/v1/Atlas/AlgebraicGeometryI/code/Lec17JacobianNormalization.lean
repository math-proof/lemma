/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec17JacobianNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.Data.Complex.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec17JacobianNormalization
set_option maxHeartbeats 800000


public noncomputable section

open Algebra AlgebraicGeometry CategoryTheory

namespace Lec17JacobianNormalization

/-- A smooth projective curve over `ℂ`: a proper, smooth, integral scheme over `Spec ℂ`
of relative dimension `1`, together with its genus. -/
structure SmoothProjectiveCurve where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isProper : IsProper structureMorphism
  isSmoothOfRelDim1 : SmoothOfRelativeDimension 1 structureMorphism
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  genus : ℕ

/-- An abelian group scheme over `ℂ`: a proper smooth scheme over `Spec ℂ` equipped with
an identity section. (Group operations are not packaged here; this captures the geometric
side used in the Abel--Jacobi statement.) -/
structure AbelianGroupScheme where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isProper : IsProper structureMorphism
  isSmooth : Smooth structureMorphism
  identitySection : SpecC ⟶ toScheme
  identitySection_comp : identitySection ≫ structureMorphism = 𝟙 SpecC

end Lec17JacobianNormalization
end
