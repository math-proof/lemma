/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Grassmannian
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Trace
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20GrassmannianTangent.Part2
set_option maxHeartbeats 400000

open KaehlerDifferential Module


@[expose] public noncomputable section

universe u v w

section Proposition35

variable (R : Type u) [CommRing R]

variable (A : Type v) [CommRing A] [Algebra R A]

/-- The tautological quotient bundle fibre `W/V` at a point `V ∈ Gr(k, W)`. -/
abbrev tautologicalQuotient (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  W ⧸ V.toSubmodule

end Proposition35
end
