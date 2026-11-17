/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Def.v1.Atlas.LieGroups.code.SyzygiesKoszul.Part3


public noncomputable section

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
