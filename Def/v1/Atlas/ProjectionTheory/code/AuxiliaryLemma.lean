/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/AuxiliaryLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.AuxiliaryLemma
open Finset


namespace IncidenceGeometry

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The set of points `(x, y) ∈ (ℤ/p)^2` satisfying the line equation `a·x + b·y = c`,
returned as a `Finset`. -/
noncomputable def AffineLine.toFinset (L : AffineLine p) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun pt => L.a * pt.1 + L.b * pt.2 = L.c)

/-- Two affine lines are considered equal when they have the same underlying point
set in `(ℤ/p)^2`. -/
def AffineLine.SamePointSet (L₁ L₂ : AffineLine p) : Prop :=
  L₁.toFinset = L₂.toFinset

/-- The "high-frequency" component of the indicator of an affine line `L` at a point
`x`: this is `1_L(x) - 1/p`, i.e. the indicator with its mean (over the plane)
subtracted. Used in the Fourier-analytic proof of the projection theorems. -/
noncomputable def AffineLine.highFreq (L : AffineLine p) (x : ZMod p × ZMod p) : ℚ :=
  if x ∈ L.toFinset then 1 - (1 : ℚ) / p else -(1 : ℚ) / p

end IncidenceGeometry
