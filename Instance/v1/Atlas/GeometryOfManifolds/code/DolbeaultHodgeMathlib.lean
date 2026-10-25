/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Def.v1.Atlas.GeometryOfManifolds.code.DolbeaultHodgeMathlib
set_option autoImplicit false

open ContinuousAlternatingMap


namespace DolbeaultHodgeMathlib

/-- Pointwise additive group structure on $k$-forms. -/
noncomputable instance instAddCommGroup (n k : ℕ) : AddCommGroup (DiffForm n k) :=
  Pi.addCommGroup

/-- Pointwise $\mathbb{R}$-module structure on $k$-forms. -/
noncomputable instance instModule (n k : ℕ) : Module ℝ (DiffForm n k) :=
  Pi.module _ _ _

end DolbeaultHodgeMathlib
