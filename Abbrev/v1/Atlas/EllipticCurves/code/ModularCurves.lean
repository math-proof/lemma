/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.ModularCurves
open Manifold

open scoped ContDiff

/-- Definition 18.4 (Complex structure): a `ComplexStructure` on a topological space
`X` is a `ChartedSpace ℂ X` together with the property that `X` is a real-analytic
manifold modelled on `ℂ` (i.e., the transition maps between charts are holomorphic). -/


section Def1915_Prerequisites

open Def1811

open scoped MatrixGroups

/-- The full modular curve `X(1) = SL₂(ℤ) \ ℍ*`. -/
noncomputable abbrev X1 : Type :=
  Quotient (MulAction.orbitRel SL(2, ℤ) ExtendedUpperHalfPlane)

end Def1915_Prerequisites
