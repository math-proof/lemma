/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.EllipticCurves.code.ModularCurves
open Manifold

open scoped ContDiff

/-- Definition 18.4 (Complex structure): a `ComplexStructure` on a topological space
`X` is a `ChartedSpace ℂ X` together with the property that `X` is a real-analytic
manifold modelled on `ℂ` (i.e., the transition maps between charts are holomorphic). -/


section Def1915_Prerequisites

open Def1811

open scoped MatrixGroups

section Lemma181

open ModularGroup UpperHalfPlane Complex Set Matrix SpecialLinearGroup

open scoped MatrixGroups

set_option maxHeartbeats 1600000

/-- An explicit triangulation of `X(1)` with `V = 3, E = 3, F = 2`, giving genus `0`
(the three vertices being the orbits of `i, ρ, ∞`). -/
noncomputable def X1.triangulation : Triangulation X1 where
  V := 3
  E := 3
  F := 2
  g := 0
  euler := by norm_num

end Lemma181
end Def1915_Prerequisites
