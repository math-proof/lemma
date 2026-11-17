/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part2

public section

noncomputable section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace LocallyFactorialDivisors

attribute [instance] HeightOnePrime.isPrime

/-- The value of `fractionalIdealToWeil` at a prime `v` is the valuation count. -/
@[simp]
lemma fractionalIdealToWeil_apply (I : FractionalIdeal R⁰ K) (v : HeightOneSpectrum R) :
    (fractionalIdealToWeil K I) v = FractionalIdeal.count K v I := by
  simp [fractionalIdealToWeil, Finsupp.ofSupportFinite]

end LocallyFactorialDivisors
end
