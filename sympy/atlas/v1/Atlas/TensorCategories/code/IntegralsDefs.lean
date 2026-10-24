/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.SimpleModule.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.DistinguishedInvertible
import Lemma.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible

set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section IntegralDefs

variable (R : Type u) [CommSemiring R] (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H]

/-- A left integral in an algebra `H` with counit is an element `I` satisfying
`x * I = ε(x) • I` for all `x ∈ H` (Definition 1.52.1). -/
structure IsLeftIntegral (I : H) : Prop where
  left_integral : ∀ (x : H), x * I = Coalgebra.counit (R := R) x • I

/-- A right integral in an algebra `H` with counit is an element `I` satisfying
`I * x = ε(x) • I` for all `x ∈ H` (Definition 1.52.1). -/
structure IsRightIntegral (I : H) : Prop where
  right_integral : ∀ (x : H), I * x = Coalgebra.counit (R := R) x • I

/-- Unfolded form of Definition 1.52.1 for left integrals: `∀ x, x * I = ε(x) • I`. -/
def Def_1_52_1_IsLeftIntegral (I : H) : Prop :=
  ∀ x : H, x * I = Coalgebra.counit (R := R) x • I

/-- Unfolded form of Definition 1.52.1 for right integrals: `∀ x, I * x = ε(x) • I`. -/
def Def_1_52_1_IsRightIntegral (I : H) : Prop :=
  ∀ x : H, I * x = Coalgebra.counit (R := R) x • I

/-- The `k`-submodule of left integrals in `H`. -/
def leftIntSubmodule : Submodule k H where
  carrier := { I : H | IsLeftIntegral k H I }
  add_mem' := by
    intro a b ha hb; exact ⟨fun x => by
      rw [mul_add, ha.left_integral x, hb.left_integral x, smul_add]⟩
  zero_mem' := ⟨fun _ => by simp⟩
  smul_mem' := by
    intro r I hI; exact ⟨fun x => by
      rw [mul_smul_comm, hI.left_integral x, smul_comm]⟩

/-- The `k`-submodule of right integrals in `H`. -/
def rightIntSubmodule : Submodule k H where
  carrier := { I : H | IsRightIntegral k H I }
  add_mem' := by
    intro a b ha hb; exact ⟨fun x => by
      rw [add_mul, ha.right_integral x, hb.right_integral x, smul_add]⟩
  zero_mem' := ⟨fun _ => by simp⟩
  smul_mem' := by
    intro r I hI; exact ⟨fun x => by
      rw [smul_mul_assoc, hI.right_integral x, smul_comm]⟩

/-- Frobenius theorem applied to integrals: the space of left integrals in a finite
dimensional quasi-Hopf algebra has dimension `1`. -/
class HasUniqueLeftIntegral where
  integral : H
  integral_isLeftIntegral : IsLeftIntegral k H integral
  integral_ne_zero : integral ≠ 0
  integral_unique : ∀ (J : H), IsLeftIntegral k H J → ∃ (c : k), J = c • integral

/-- Typeclass packaging the existence of a distinguished, essentially unique nonzero
right integral in `H`. -/
class HasUniqueRightIntegral where
  integral : H
  integral_isRightIntegral : IsRightIntegral k H integral
  integral_ne_zero : integral ≠ 0
  integral_unique : ∀ (J : H), IsRightIntegral k H J → ∃ (c : k), J = c • integral

/-- Every finite dimensional quasi-Hopf algebra has a distinguished left integral
extracted via choice from `prop_1_52_3_left`. -/
end Prop1523

section Prop1525

variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Algebra R H] [Coalgebra R H]

/-- The distinguished character `χ : H →ₗ[R] R` associated to a left integral `I`,
characterized by the right multiplication law `I * x = χ(x) • I`. -/
structure DistinguishedCharacter (I : H) where
  χ : H →ₗ[R] R
  left_int : IsLeftIntegral R H I
  right_law : ∀ (x : H), I * x = χ x • I

/-- An algebra is unimodular when every left integral is also a right integral
(Definition 1.52.6 at the algebra level). -/
def IsUnimodularAlgebra : Prop :=
  ∀ (I : H), IsLeftIntegral R H I → IsRightIntegral R H I

end DistinguishedCharacter


section Proposition_1_52_4

open CategoryTheory

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/-- Categorical data needed to state Proposition 1.52.4: a procedure constructing
the one dimensional representation associated to a character, plus the agreement
between the distinguished invertible object and that representation. -/
class Prop1524Data
    (C : Type*) [Category C] [MonoidalCategory C] [RigidCategory C]
    [HasDistinguishedInvertibleData C] [FiniteDimensional k H] where
  oneDimChar : (H →ₗ[k] k) → C
  lρ_iso_distinguishedChar :
    ∀ (I : H) (_hI : I ≠ 0) (dc : DistinguishedCharacter k H I),
      Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ oneDimChar dc.χ)

/-- Alias for `Prop1524Data` used when `C = Rep(H)`. -/
abbrev Prop1524RepData := Prop1524Data

end Proposition_1_52_4


section Prop1524_consequences

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]
