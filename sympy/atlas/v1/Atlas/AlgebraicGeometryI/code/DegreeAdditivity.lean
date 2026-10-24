/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Length
import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.LinearAlgebra.ExteriorPower.Basis

noncomputable section

open Submodule

namespace DegreeAdditivity

/-- The "torsion degree" of a module `M` over a domain `R`, defined as the length of its
torsion submodule. Plays the role of `ℓ(𝒯)` in the degree additivity statement. -/
def torsionDegree (R : Type*) (M : Type*)
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (torsion R M)

/-- Data of a short exact sequence of `R`-modules `0 → N → M → P → 0`, suitable as a defining
relation in `K₀(R)`. -/
structure K0SESRelation (R : Type*) [Ring R] where
  N : Type*
  M : Type*
  P : Type*
  [instN : AddCommGroup N]
  [modN : Module R N]
  [instM : AddCommGroup M]
  [modM : Module R M]
  [instP : AddCommGroup P]
  [modP : Module R P]
  f : N →ₗ[R] M
  g : M →ₗ[R] P
  f_inj : Function.Injective f
  g_surj : Function.Surjective g
  exact : Function.Exact f g

attribute [instance] K0SESRelation.instN K0SESRelation.modN
  K0SESRelation.instM K0SESRelation.modM K0SESRelation.instP K0SESRelation.modP
