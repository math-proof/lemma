/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import sympy.atlas.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxHeartbeats 800000

open Finset Complex

/-- A `*`-algebra with trace: an associative ℂ-algebra with a star structure, a linear trace
satisfying `τ(ab) = τ(ba)`, and a positive definiteness condition `0 < Re τ(a * star a)` for
`a ≠ 0`. -/
structure StarAlgWithTrace where
  carrier : Type*
  [instRing : Ring carrier]
  [instAlgebra : Algebra ℂ carrier]
  [instStarRing : StarRing carrier]
  [instStarModule : StarModule ℂ carrier]
  trace : carrier →ₗ[ℂ] ℂ
  trace_comm : ∀ a b, trace (a * b) = trace (b * a)
  trace_pos_def : ∀ a, a ≠ 0 → 0 < (trace (a * star a)).re

attribute [instance] StarAlgWithTrace.instRing StarAlgWithTrace.instAlgebra
  StarAlgWithTrace.instStarRing StarAlgWithTrace.instStarModule

/-- Definition 1.43.1: A `*`-algebra is an associative algebra `B` over `ℂ` with an antilinear
anti-involution and a trace functional whose Hermitian form is positive definite. -/
abbrev Definition_1_43_1 := StarAlgWithTrace

namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

/-- A finite-dimensional ℂ-algebra is Artinian as a ring. -/
instance [FiniteDimensional ℂ B.carrier] : IsArtinianRing B.carrier :=
  isArtinian_of_tower ℂ inferInstance

/-- The duality map `star : ι → ι` packaged as an `Equiv` using its involutivity. -/
def starEquivC : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- The complex-coefficient multiplication on the Grothendieck ring of a fusion ring,
expanded against the structure constants `N i j k`. -/
def grMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- The complex-coefficient star on `ι → ℂ`: complex-conjugate the coefficient and dualise the
index via `R.star`. -/
def grStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace on `ι → ℂ`: take the coefficient at the unit basis vector. -/
def grTraceC (f : ι → ℂ) : ℂ := f R.unit

/-- The duality map on indices of a multifusion ring, packaged as an `Equiv`. -/
def starEquivC' : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- Multiplication on the complexified multifusion ring, expanded against structure constants. -/
def grMulC' (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- The star map on the complexified multifusion ring: conjugate the coefficient and dualise
the index. -/
def grStarC' (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace on the complexified multifusion ring: sum coefficients over the indecomposable
units `I₀`. -/
def grTraceC' (f : ι → ℂ) : ℂ :=
  ∑ k ∈ R.I₀, f k

/-- Proposition 1.43.4: the complexification of a (multifusion) based ring is canonically a
`*`-algebra: star is involutive, anti-multiplicative, the trace is symmetric, and the Hermitian
form is positive definite. -/
theorem Proposition_1_43_4 :

    (∀ f : ι → ℂ, R.grStarC' (R.grStarC' f) = f) ∧

    (∀ f g : ι → ℂ, R.grStarC' (R.grMulC' f g) = R.grMulC' (R.grStarC' g) (R.grStarC' f)) ∧

    (∀ a b : ι → ℂ, R.grTraceC' (R.grMulC' a b) = R.grTraceC' (R.grMulC' b a)) ∧

    (∀ a : ι → ℂ, a ≠ 0 → 0 < (R.grTraceC' (R.grMulC' a (R.grStarC' a))).re) :=
  ⟨R.grStarC'_invol, R.grStarC'_anti_mul, R.trace_comm_grC', R.trace_pos_def_grC'⟩

end

end MultifusionRingDef
