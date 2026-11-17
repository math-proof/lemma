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
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors.Part2

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace LinearEquivDivisors

variable {Y : Type*}

/-- Linear equivalence of Weil divisors modulo a chosen subgroup `P` of principal
divisors: `D₁ ~ D₂` iff `D₁ - D₂ ∈ P` (Def 32, Lec 16). -/
def WeilLinearlyEquivalent (P : PrincipalDivisors Y) (D₁ D₂ : WeilDivisorGroup Y) :
    Prop :=
  D₁ - D₂ ∈ P


end LinearEquivDivisors
end
