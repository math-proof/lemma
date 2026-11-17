/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.ClassGroup
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank


@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace LinearEquivDivisors

/-- The group of Weil divisors on `Y` as finitely supported functions `Y → ℤ`. -/
abbrev WeilDivisorGroup (Y : Type*) := Y →₀ ℤ

end LinearEquivDivisors
end
