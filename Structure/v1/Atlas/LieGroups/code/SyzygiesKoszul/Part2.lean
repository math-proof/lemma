/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Def.v1.Atlas.LieGroups.code.SyzygiesKoszul.Part3


noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

variable (k : Type*) [Field k] (n : ℕ)

local notation "R" => MvPolynomial (Fin n) k

structure KoszulComplex (k : Type*) [Field k] (n : ℕ) where
  rank : (p : ℕ) → (hp : p ≤ n) → ℕ
  rank_eq : ∀ (p : ℕ) (hp : p ≤ n), rank p hp = Nat.choose n p
  differential : ∀ (p : ℕ) (hp : 0 < p) (hp' : p ≤ n),
    ((Fin (rank p hp') → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
     (Fin (rank (p - 1) (by omega)) → MvPolynomial (Fin n) k))
  d_squared_zero : ∀ (p : ℕ) (hp : 1 < p) (hp' : p ≤ n),
    (differential (p - 1) (by omega) (by omega)).comp
      (differential p (by omega) hp') = 0

end
