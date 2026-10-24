/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4FiniteMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Topology.KrullDimension

open AlgebraicGeometry PrimeSpectrum TopologicalSpace Set

universe u

namespace Lec4

/-- Lecture 4, Definition 9: affine morphism of schemes, defined here in terms of Mathlib's
`IsAffineHom`. -/
abbrev IsAffineMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  IsAffineHom f

/-- Lecture 4, Definition 10: a *finite morphism* of schemes, defined here as Mathlib's
`IsFinite f`. -/
abbrev IsFiniteMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  IsFinite f

/-- Convenience wrapper: the topological Krull dimension of `T`, used here as the Lec 4 notion
of dimension. -/
noncomputable abbrev krullDim_def (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  topologicalKrullDim T

end Lec4
