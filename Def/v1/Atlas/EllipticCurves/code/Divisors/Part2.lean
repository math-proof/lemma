/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Theorem.v1.Atlas.EllipticCurves.code.Divisors


noncomputable section

open Finsupp

variable {P : Type*}

namespace CurveDiv

/-- The degree map `Div C → ℤ` packaged as an additive group homomorphism. -/
def degHom (P : Type*) : CurveDiv P →+ ℤ where
  toFun := deg
  map_zero' := deg_zero
  map_add' := deg_add

/-- The subgroup `Div⁰ C` of divisors of degree zero, defined as the kernel of
the degree map. (Cf. Definition 23.13.) -/
def DivZero (P : Type*) : AddSubgroup (CurveDiv P) :=
  AddMonoidHom.ker (degHom P)

end CurveDiv
end
