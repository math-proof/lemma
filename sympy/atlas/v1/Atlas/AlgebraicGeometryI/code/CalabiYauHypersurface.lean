/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic

set_option maxHeartbeats 400000

namespace CYHyp

/-- Auxiliary record of numerical invariants of a smooth complete curve: its genus `g` and
canonical degree `degK`. -/
structure SmoothCompleteCurve' where
  g : ℤ
  degK : ℤ

/-- Build a `SmoothCompleteCurve'` of genus `g` with canonical degree `2g - 2`. -/
def mkCurve' (g : ℕ) : SmoothCompleteCurve' where
  g := g
  degK := 2 * (g : ℤ) - 2

/-- Arithmetic genus of a smooth plane curve of degree `d`: `(d-1)(d-2)/2`. -/
def genus_plane_curve (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

/-- Compatibility between the natural-number and integer formulations of the plane-curve genus. -/
end CYHyp

open CYHyp

noncomputable section

/-- A smooth projective hypersurface in `P^n` of degree `d`, with `n, d ≥ 1`. -/
structure SmoothProjectiveHypersurface where
  n : ℕ
  d : ℕ
  hn : 1 ≤ n
  hd : 1 ≤ d

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
