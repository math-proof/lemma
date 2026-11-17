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
public import Def.v1.Atlas.LieGroups.code.SyzygiesKoszul


public noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

structure IsGradedSModule {k S M : Type*} [CommRing k] [Ring S] [Algebra k S]
    [AddCommGroup M] [Module S M] [Module k M] [IsScalarTower k S M]
    (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮]
    (ℳ : ℕ → Submodule k M) : Prop where
  internal : DirectSum.IsInternal ℳ
  smul_mem : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j)

end
