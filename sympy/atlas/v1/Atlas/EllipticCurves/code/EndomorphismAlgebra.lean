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
import sympy.atlas.v1.Atlas.EllipticCurves.code.TorsionEndomorphism
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.GroupTheory.Archimedean
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-- A subring `O` of a `ℚ`-algebra `A` is an order if it is finitely generated as a
`ℤ`-module and its `ℚ`-span fills `A` (cf. Definition 12.22 of "Elliptic Curves"). -/
structure IsOrder (A : Type*) [Ring A] [Algebra ℚ A] (O : Subring A) : Prop where
  fg_zmul : (O.toAddSubgroup.toIntSubmodule).FG
  span_eq_top : Submodule.span ℚ (O : Set A) = ⊤

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

end ConductorOrder

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

/-- Convenient abbreviation for the quaternion algebra `ℍ[k, a, b]` with both
nonvanishing parameters `a, b ∈ k×`. -/
abbrev QAlgebra (k : Type*) [Field k] (a b : k) (_ : a ≠ 0) (_ : b ≠ 0) := ℍ[k, a, b]

variable {k : Type*} [Field k] (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)

/-- The standard basis element `i` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qI : ℍ[k, a, b] := ⟨0, 1, 0, 0⟩

/-- The standard basis element `j` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qJ : ℍ[k, a, b] := ⟨0, 0, 1, 0⟩

/-- The standard basis element `k = i·j` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qK : ℍ[k, a, b] := ⟨0, 0, 0, 1⟩

/-- Synonym: `ℍ[k, a, b]` is a ring (recorded for use later). -/
instance : Ring ℍ[k, a, b] := inferInstance

/-- Synonym: `ℍ[k, a, b]` is a `k`-algebra. -/
instance : Algebra k ℍ[k, a, b] := inferInstance

/-- The reduced trace `T γ = 2 · Re γ` on the quaternion algebra `ℍ[k, a, b]`
(Definition 12.6). -/
def reducedTrace {k : Type*} [Field k] (a b : k) (γ : ℍ[k, a, b]) : k :=
  2 * γ.re

/-- The standard `k`-basis `{1, i, j, k}` of the quaternion algebra `ℍ[k, a, b]`. -/
noncomputable def basis : Basis (Fin 4) k ℍ[k, a, b] :=
  QuaternionAlgebra.basisOneIJK a 0 b

/-- The packaged `QuaternionAlgebra.Basis` structure for `ℍ[k, a, b]` itself. -/
def quatBasis : QuaternionAlgebra.Basis ℍ[k, a, b] a 0 b :=
  QuaternionAlgebra.Basis.self k

noncomputable example : DivisionRing (Quaternion ℝ) :=
  Quaternion.instDivisionRing

/-- The reduced norm `N γ = (γ · γ̄).re` on the quaternion algebra `ℍ[k, a, b]`
(Definition 12.6). -/
def reducedNorm {k : Type*} [Field k] (a b : k) (γ : ℍ[k, a, b]) : k :=
  (γ * star γ).re

/-- Every quaternion algebra `ℍ[k, a, b]` is nontrivial. -/
instance quatAlg_nontrivial {k : Type*} [Field k] (a b : k) :
    Nontrivial ℍ[k, a, b] :=
  ⟨⟨0, 1, by simp⟩⟩
