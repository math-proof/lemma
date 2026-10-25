/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Structure.v1.Atlas.AlgebraicGeometryI.code.CalabiYauHypersurface.Part2
set_option maxHeartbeats 400000

open CYHyp


noncomputable section

namespace SmoothProjectiveHypersurface

/-- Canonical twist `d - n - 1` of a smooth hypersurface `Y ⊂ P^n` of degree `d` (so
`K_Y = O_Y(d - n - 1)` by the adjunction formula). -/
def canonicalTwist (Y : SmoothProjectiveHypersurface) : ℤ :=
  (Y.d : ℤ) - (Y.n : ℤ) - 1

/-- Degree of the canonical bundle of `Y`: `d · (d - n - 1)`. -/
def degCanonical (Y : SmoothProjectiveHypersurface) : ℤ :=
  (Y.d : ℤ) * Y.canonicalTwist

/-- Calabi-Yau predicate for a hypersurface: `d = n + 1`, equivalent to trivial canonical bundle. -/
def isCalabiYau (Y : SmoothProjectiveHypersurface) : Prop :=
  Y.d = Y.n + 1

/-- The smooth cubic in `P²` (an elliptic curve) as a `SmoothProjectiveHypersurface`. -/
def ellipticCurve : SmoothProjectiveHypersurface :=
  { n := 2, d := 3, hn := by omega, hd := by omega }

/-- A smooth quartic in `P³`, i.e. a K3 surface, as a `SmoothProjectiveHypersurface`. -/
def K3surface : SmoothProjectiveHypersurface :=
  { n := 3, d := 4, hn := by omega, hd := by omega }

/-- A smooth quintic in `P⁴`, i.e. a Calabi-Yau threefold, as a `SmoothProjectiveHypersurface`. -/
def CY3fold : SmoothProjectiveHypersurface :=
  { n := 4, d := 5, hn := by omega, hd := by omega }

/-- The plane-curve canonical degree computed from the genus matches the hypersurface formula. -/
def degK_hypersurface (n : ℤ) (d : ℤ) : ℤ := d * (d - (n + 1))

end SmoothProjectiveHypersurface
end
