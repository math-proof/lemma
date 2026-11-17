/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.ClassGroup
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal


@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace DivisorsPicard

/-- The Weil divisor group `DW(Y)` on `Y` (Def 29, Lec 14): finitely supported `ℤ`-valued
formal sums on `Y`, viewed as the free abelian group on points of `Y`. -/
abbrev WeilDivisorGroup (Y : Type*) := Y →₀ ℤ

end DivisorsPicard
end
