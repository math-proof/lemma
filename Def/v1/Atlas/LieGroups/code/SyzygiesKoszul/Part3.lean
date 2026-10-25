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
import Notation.v1.Atlas.LieGroups.code.SyzygiesKoszul


noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

variable (k : Type*) [Field k] (n : ℕ)

local notation "R" => MvPolynomial (Fin n) k

def augmentation_ideal_poly : Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))

def quotientGrading {k' S : Type*} [CommRing k'] [CommRing S] [Algebra k' S]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    (ℳ : ℕ → Submodule k' M) (i : ℕ) :
    Submodule k' (M ⧸ (augmentationIdealGraded 𝒮 • (⊤ : Submodule S M))) :=
  (ℳ i).map ((augmentationIdealGraded 𝒮 • (⊤ : Submodule S M)).mkQ.restrictScalars k')

end
