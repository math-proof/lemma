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
public import Structure.v1.Atlas.LieGroups.code.SyzygiesKoszul

@[expose] public section

noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

def IsConnectedGrading (k : Type*) (S : Type*) [CommRing k] [Ring S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮] : Prop :=
  𝒮 0 = (Algebra.linearMap k S).range

def augmentationIdealGraded {k S : Type*} [CommRing k] [CommRing S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮] : Ideal S :=
  Ideal.span (⋃ (i : ℕ) (_ : 0 < i), ↑(𝒮 i))

def hilbertSeries {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (ℳ : ℕ → Submodule k M) : PowerSeries ℤ :=
  PowerSeries.mk (fun i => (Module.finrank k (ℳ i) : ℤ))

end
