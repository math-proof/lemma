/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
open Polynomial Finset


namespace BerlekampRabin

section Defs

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Two nonzero elements `α`, `β` of a finite field `F` are of *different type* if
their `(q-1)/2`-th powers differ, where `q = |F|`. By Euler's criterion this means
exactly one of `α, β` is a quadratic residue. -/
def DifferentType (α β : F) : Prop :=
  α ≠ 0 ∧ β ≠ 0 ∧ α ^ (Fintype.card F / 2) ≠ β ^ (Fintype.card F / 2)

end Defs
end BerlekampRabin
