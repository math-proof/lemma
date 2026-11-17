/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentSpaceDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Algebra.Module.SpanRankOperations
set_option maxHeartbeats 400000

public section

noncomputable section

open IsLocalRing Module

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

end
