/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupChart.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

open Polynomial


/-- Ring map on `k[X][Y]` substituting `Y ↦ C(X) · Y`, modelling one affine chart of the
blow-up of the affine plane at the origin (where the exceptional `y`-coordinate is replaced
by the product of the base coordinate `X` and a new fibre coordinate `Y`). -/
noncomputable def blowupChartMap (k : Type*) [CommRing k] :
    Polynomial (Polynomial k) →+* Polynomial (Polynomial k) :=
  eval₂RingHom C (C X * X)

