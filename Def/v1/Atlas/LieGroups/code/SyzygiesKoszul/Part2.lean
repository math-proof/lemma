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
import Structure.v1.Atlas.LieGroups.code.SyzygiesKoszul


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
