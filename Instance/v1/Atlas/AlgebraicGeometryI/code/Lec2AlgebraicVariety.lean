/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AlgebraicVariety.lean -/

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
import Instance.v1.Atlas.AlgebraicGeometryI.code.AffineVarietyDef
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.AffineVarietyDef
import Class.v1.Atlas.AlgebraicGeometryI.code.Lec2AlgebraicVariety
set_option maxHeartbeats 800000


namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

attribute [instance] IsAlgebraicVariety.isReduced IsAlgebraicVariety.locallyOfFiniteType

/-- Every affine variety over `k` is in particular an algebraic variety, with the trivial
finite affine cover by `X` itself. -/
instance IsAffineVariety.toIsAlgebraicVariety {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [h : IsAffineVariety k X] : IsAlgebraicVariety k X where
  isReduced := h.isReduced
  locallyOfFiniteType := h.locallyOfFiniteType
  hasFiniteAffineCover := by
    haveI : IsAffine X := ⟨h.toSpecΓ_isIso⟩
    exact ⟨PUnit.{u+1}, inferInstance, fun _ => ⊤,
      fun _ => isAffineOpen_top X, by simp⟩

end AlgebraicGeometry.Scheme
