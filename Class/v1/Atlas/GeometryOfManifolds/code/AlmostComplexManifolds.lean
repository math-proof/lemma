/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


/-- A typeclass abstracting a notion of positivity on a real vector space: a predicate
`IsPositive` closed under addition and positive scaling, with nonzero positive elements. -/
class HasPositivity (α : Type*) [AddCommGroup α] [Module ℝ α] where
  IsPositive : α → Prop
  pos_add : ∀ a b, IsPositive a → IsPositive b → IsPositive (a + b)
  pos_smul_pos : ∀ (r : ℝ) a, 0 < r → IsPositive a → IsPositive (r • a)
  pos_nonzero : ∀ a, IsPositive a → a ≠ 0


