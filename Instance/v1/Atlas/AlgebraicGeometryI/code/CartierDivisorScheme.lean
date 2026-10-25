/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.GroupTheory.QuotientGroup.Basic
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace CartierDivisorScheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every integral scheme has a nonempty underlying topological space (since it is irreducible). -/
noncomputable instance instNonemptyIntegralScheme : Nonempty X := by
  have : IrreducibleSpace X := inferInstance; exact ⟨this.2.some⟩

/-- The top open set `⊤` of an integral scheme is nonempty. -/
noncomputable instance instNonemptyTop : Nonempty (⊤ : X.Opens) :=
  ⟨⟨(inferInstance : Nonempty X).some, trivial⟩⟩

end CartierDivisorScheme
