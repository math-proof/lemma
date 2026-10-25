/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TrivialDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
set_option autoImplicit false


/-- Trivial differential-form scaffolding: every degree's space of forms is the singleton
`PUnit`, providing a degenerate witness for the DFS API. -/
@[reducible]
def TrivialΩ : ℕ → Type* := fun _ => PUnit

/-- Trivial vector-field space: the singleton `PUnit`, the partner of `TrivialΩ`. -/
@[reducible]
def TrivialVF : Type* := PUnit

