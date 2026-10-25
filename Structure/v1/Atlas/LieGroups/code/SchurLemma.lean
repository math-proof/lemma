/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula


noncomputable section

open scoped ComplexOrder

structure FinDimRep (G : Type*) [Group G] (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] where
  toMonoidHom : G →* (V →ₗ[ℂ] V)

end
