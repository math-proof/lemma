/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SingularLocus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.Locus

noncomputable section

open AlgebraicGeometry Algebra

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K]

/-- The **singular locus** of a morphism `f : X → Spec K` is the complement of
the smooth locus, i.e., the set of points where `f` fails to be smooth. -/
def singularLocus (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] : Set X :=
  (f.smoothLocus : Set X)ᶜ

/-- Algebraic version of `singularLocus`: for a `K`-algebra `A`, the singular
locus is the complement of the smooth locus inside `Spec A`. -/
def singularLocusAlg (K : Type*) [Field K] (A : Type*) [CommRing A]
    [Algebra K A] : Set (PrimeSpectrum A) :=
  (Algebra.smoothLocus K A)ᶜ
