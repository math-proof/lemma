/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop24DegreePicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Polynomial.Quotient
open Polynomial


noncomputable section

namespace Prop24Picard

variable {Y : Type*}

/-- Weil divisors on a curve `Y`: finitely supported integer-valued functions on the
underlying point set. -/
abbrev WeilDiv (Y : Type*) := Y →₀ ℤ

end Prop24Picard
end
