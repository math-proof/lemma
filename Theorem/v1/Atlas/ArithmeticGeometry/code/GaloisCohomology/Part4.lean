/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.MulAction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.SeparableClosure
import Instance.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part5
open groupCohomology


namespace ContCrossedHom

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]
    [TopologicalSpace G] [TopologicalSpace A]

omit [ContinuousAdd A] [ContinuousNeg A] in
/-- The zero continuous crossed hom evaluates to $0$ everywhere. -/
@[simp] theorem zero_apply (g : G) : (0 : ContCrossedHom G A) g = 0 := rfl

omit [ContinuousNeg A] in
/-- Sum of two continuous crossed homs evaluates pointwise. -/
@[simp] theorem add_apply (α β : ContCrossedHom G A) (g : G) :
    (α + β) g = α g + β g := rfl

omit [ContinuousAdd A] in
/-- Negation of a continuous crossed hom evaluates pointwise. -/
@[simp] theorem neg_apply (α : ContCrossedHom G A) (g : G) : (-α) g = -(α g) := rfl

end ContCrossedHom
