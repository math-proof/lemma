/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Over


namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry CategoryTheory

universe u

/-- An *affine variety* over a field `k` (Def 2, Lec 2): a scheme `X` over `Spec k` that is
isomorphic to `Spec Γ(X, O_X)`, is locally of finite type over `k`, and is reduced. -/
class IsAffineVariety (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    Prop where
  toSpecΓ_isIso : IsIso X.toSpecΓ
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ Spec (.of k))
  isReduced : AlgebraicGeometry.IsReduced X

end AlgebraicGeometry.Scheme
