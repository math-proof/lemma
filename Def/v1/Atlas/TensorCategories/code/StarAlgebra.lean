/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Instance.v1.Atlas.TensorCategories.code.StarAlgebra
set_option maxHeartbeats 800000

open Finset Complex

attribute [instance] StarAlgWithTrace.instRing StarAlgWithTrace.instAlgebra
  StarAlgWithTrace.instStarRing StarAlgWithTrace.instStarModule


namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

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

end
end
end StarAlgWithTrace
