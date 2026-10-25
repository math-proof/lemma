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
import Structure.v1.Atlas.EllipticCurves.code.Divisors


noncomputable section

open Finsupp

variable {P : Type*}

namespace CurveDiv

attribute [instance] FunctionFieldDiv.instCommGroup

variable (Φ : FunctionFieldDiv P)

/-- The subgroup `Princ C ⊆ Div C` of principal divisors, defined as the image
of the function-field divisor map. (Definition 23.13.) -/
def PrincDiv : AddSubgroup (CurveDiv P) :=
  AddMonoidHom.range Φ.divMap

end CurveDiv
end
