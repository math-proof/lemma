/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
set_option maxHeartbeats 400000


@[expose] public noncomputable section

open KaehlerDifferential TensorProduct

namespace SmoothClosedSubvariety

section Corollary25

variable (k : Type*) [Field k]

variable (R : Type*) [CommRing R] [Algebra k R]

variable (I : Ideal R)

/-- The normal module `N_{Z/X} = Hom_{R⧸I}(I/I², R⧸I)`, dual to the conormal module `I/I²`. -/
abbrev NormalModule (R : Type*) [CommRing R] (I : Ideal R) : Type _ :=
  Module.Dual (R ⧸ I) I.Cotangent

end Corollary25
end SmoothClosedSubvariety
end
