/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Algebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.GroupTheory.Archimedean
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Structure.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra
open NumberField


/-- The order of conductor `f` in `ℤ[√d]`: the subring consisting of all elements
whose imaginary part is divisible by `f`. -/
def conductorOrder (d : ℤ) (f : ℕ) : Subring (ℤ√d) where
  carrier := { z | (f : ℤ) ∣ z.im }
  zero_mem' := dvd_zero _
  one_mem' := dvd_zero _
  add_mem' ha hb := dvd_add ha hb
  mul_mem' ha hb := by
    show (f : ℤ) ∣ _
    exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_left ha _)
  neg_mem' ha := dvd_neg.mpr ha

/-- The "imaginary part" homomorphism `ℤ[√d] →+ ℤ` sending `a + b√d ↦ b`. -/
def imAddHom (d : ℤ) : ℤ√d →+ ℤ where
  toFun z := z.im
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The discriminant of the conductor `f` order in `ℤ[√d]`, defined as `4 · f² · d`. -/
def orderDiscriminant (d : ℤ) (f : ℕ) : ℤ := 4 * (f : ℤ) ^ 2 * d

/-- The discriminant of the maximal order in `ℤ[√d]` (conductor `1`), which is `4d`. -/
def maximalDiscriminant (d : ℤ) : ℤ := 4 * d

open scoped Quaternion

open Module

section QuaternionAlg

/-- A `k`-algebra `H` is a quaternion algebra (Definition 12.12) if it has a basis of
the form `{1, α, β, αβ}` with `α², β² ∈ k×` and `αβ = -βα`, equivalently encoded here
via the existence of anticommuting elements with nonzero scalar squares and
`finrank k H = 4`. -/
def IsQuaternionAlgebra (k : Type*) [Field k] (H : Type*)
    [Ring H] [Algebra k H] : Prop :=
  ∃ (α β : H),
    (∃ a : k, a ≠ 0 ∧ α * α = algebraMap k H a) ∧
    (∃ b : k, b ≠ 0 ∧ β * β = algebraMap k H b) ∧
    α * β = -(β * α) ∧
    Module.finrank k H = 4

end QuaternionAlg
