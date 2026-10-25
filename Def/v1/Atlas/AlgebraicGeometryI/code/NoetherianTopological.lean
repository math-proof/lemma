/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherianTopological.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.NoetherianSpace
import Mathlib.Order.Minimal
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Order.KrullDimension
open TopologicalSpace Set

universe u


namespace NoetherianTopological

/-- A preorder is catenary if any two saturated chains with the same endpoints have
the same length. -/
def IsCatenary (α : Type*) [Preorder α] : Prop :=
  ∀ (s₁ s₂ : LTSeries α),

    s₁.toFun 0 = s₂.toFun 0 →

    s₁.toFun (Fin.last s₁.length) = s₂.toFun (Fin.last s₂.length) →

    (∀ i : Fin s₁.length, s₁.toFun i.castSucc ⋖ s₁.toFun i.succ) →

    (∀ i : Fin s₂.length, s₂.toFun i.castSucc ⋖ s₂.toFun i.succ) →

    s₁.length = s₂.length

/-- A commutative ring is catenary if its prime spectrum is a catenary poset. -/
def IsRingCatenary (R : Type*) [CommRing R] : Prop :=
  IsCatenary (PrimeSpectrum R)

end NoetherianTopological
