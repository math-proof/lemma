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
set_option maxHeartbeats 800000


namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- An algebraic variety over `k` (Definition 3 of Lecture 2): a reduced scheme `X` over
`Spec k` that is locally of finite type and admits a finite affine open cover. -/
class IsAlgebraicVariety (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] : Prop where
  isReduced : AlgebraicGeometry.IsReduced X
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ Spec (.of k))
  hasFiniteAffineCover : ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
    (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, (U i) = ⊤)

end AlgebraicGeometry.Scheme
