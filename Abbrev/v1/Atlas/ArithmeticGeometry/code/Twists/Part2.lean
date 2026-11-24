module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
public import Def.v1.Atlas.ArithmeticGeometry.code.Twists.Part2
open AlgebraicGeometry CategoryTheory Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u


namespace ArithmeticGeometry

variable (k : Type u) [Field k]

variable {k}

/-- The ring homomorphism $\mathrm{ULift}\, \mathbb{Q} \to \mathbb{Q}$ coming
from the canonical equivalence. A universe-polymorphism utility. -/
noncomputable abbrev uliftQToQ : ULift.{v, 0} ℚ →+* ℚ :=
  (ULift.ringEquiv (R := ℚ)).toRingHom


end ArithmeticGeometry
