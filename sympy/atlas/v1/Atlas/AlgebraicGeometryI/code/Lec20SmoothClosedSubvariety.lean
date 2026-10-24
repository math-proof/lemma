/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

set_option maxHeartbeats 400000

noncomputable section

open KaehlerDifferential TensorProduct

namespace SmoothClosedSubvariety

section Corollary25

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable (I : Ideal R)

/-- The normal module `N_{Z/X} = Hom_{R⧸I}(I/I², R⧸I)`, dual to the conormal module `I/I²`. -/
abbrev NormalModule (R : Type*) [CommRing R] (I : Ideal R) : Type _ :=
  Module.Dual (R ⧸ I) I.Cotangent
