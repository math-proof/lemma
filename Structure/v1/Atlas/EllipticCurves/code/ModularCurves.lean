/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.ModularCurves.Part2
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

/-- A combinatorial triangulation of a topological space, recording the number of
vertices `V`, edges `E`, faces `F`, and genus `g`, subject to the Euler characteristic
identity `V - E + F = 2 - 2g`. -/
structure Triangulation (X : Type*) [TopologicalSpace X] where
  V : ℕ
  E : ℕ
  F : ℕ
  g : ℕ
  euler : V + F + 2 * g = E + 2

end Lemma181
end Def1915_Prerequisites
