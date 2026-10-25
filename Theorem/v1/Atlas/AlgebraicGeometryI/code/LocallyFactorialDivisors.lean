/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.ClassGroup
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part2


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
