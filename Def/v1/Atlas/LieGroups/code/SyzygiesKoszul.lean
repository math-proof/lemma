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

@[expose] public section

noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

def IsRegularSequence {A : Type*} [CommRing A] {m : ℕ} (f : Fin m → A) : Prop :=
  (∀ (j : Fin m),
    ∀ (r : A ⧸ Ideal.span (Set.image f {i | (i : ℕ) < j})),
      r ≠ 0 →
        (Ideal.Quotient.mk (Ideal.span (Set.image f {i | (i : ℕ) < j})) (f j)) • r ≠ 0) ∧
  Nontrivial (A ⧸ Ideal.span (Set.range f))

end
