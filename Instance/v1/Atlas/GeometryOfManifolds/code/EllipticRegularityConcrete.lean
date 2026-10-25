/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityConcrete
set_option autoImplicit false


namespace EllipticRegularityConcrete

/-- Pointwise addition gives `DiffForm n k` the structure of an additive abelian group. -/
noncomputable instance instAddCommGroup (n k : ℕ) : AddCommGroup (DiffForm n k) :=
  Pi.addCommGroup

/-- Pointwise scalar multiplication gives `DiffForm n k` the structure of an $\mathbb{R}$-module. -/
noncomputable instance instModule (n k : ℕ) : Module ℝ (DiffForm n k) :=
  Pi.module _ _ _


end EllipticRegularityConcrete
