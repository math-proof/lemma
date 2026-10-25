/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorem.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors


noncomputable section

open scoped nonZeroDivisors

namespace LinearEquivDivisors

variable {Y : Type*}

/-- The setoid on Weil divisors given by linear equivalence relative to `P`. -/
def weilLinearEquivSetoid (P : PrincipalDivisors Y) :
    Setoid (WeilDivisorGroup Y) :=
  ⟨WeilLinearlyEquivalent P, weilLinearlyEquivalent_equivalence P⟩


/-- The degree of a Weil divisor is the sum of its coefficients. -/
def WeilDivisor.degree (D : WeilDivisorGroup Y) : ℤ :=
  D.sum (fun _ n => n)


/-- The complete linear system `|D|`: all effective Weil divisors linearly
equivalent to `D`. -/
def completeLinearSystem (P : PrincipalDivisors Y) (D : WeilDivisorGroup Y) :
    Set (WeilDivisorGroup Y) :=
  {D' | WeilDivisor.IsEffective D' ∧ WeilLinearlyEquivalent P D' D}


/-- Dimension of a complete linear system, defined as `dim_k V - 1` where `V`
is the global sections module. -/
def completeLinearSystemDim (k : Type*) [Field k] (V : Type*)
    [AddCommGroup V] [Module k V] [Module.Finite k V] : ℤ :=
  (Module.finrank k V : ℤ) - 1

end LinearEquivDivisors
end
