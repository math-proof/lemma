/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

universe w v u

namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- Left quantum trace of an endo-like morphism `a : V ⟶ (Vᘁ)ᘁ` in a rigid category: the
composite `η_V V* ≫ (a ▷ V*) ≫ ε_{V*} (V*)*`. -/
noncomputable def leftQuantumTrace {V : C} (a : V ⟶ (Vᘁ)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

/-- Right quantum trace of an endo-like morphism `a : V ⟶ *(*V)` in a rigid category, dual
to `leftQuantumTrace`. -/
noncomputable def rightQuantumTrace {V : C} (a : V ⟶ ᘁ(ᘁV)) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ (ᘁV) V ≫ ((ᘁV : C) ◁ a) ≫ ε_ (ᘁ(ᘁV)) (ᘁV)

/-- Additivity of the left quantum trace over a short exact sequence `0 → W → V → Q → 0`
compatible with the chosen morphisms into the double duals. -/
structure PivotalStructure where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  tensorCoherenceIso : ∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ
  monoidality : ∀ (V W : C),
    (pivotalIso (V ⊗ W)).hom =
      ((pivotalIso V).hom ⊗ₘ (pivotalIso W).hom) ≫ (tensorCoherenceIso V W).hom
  dimUnit : leftQuantumTrace C (pivotalIso (𝟙_ C)).hom = 𝟙 (𝟙_ C)

/-- EGNO Definition 1.38.1: synonym for `PivotalStructure`. -/
abbrev def_1_38_1 := PivotalStructure C

section Def_1_38_1_Conditions

variable {C}

end Def_1_38_1_Conditions

/-- Class form of `PivotalStructure`: a pivotal structure on a rigid monoidal category as
a typeclass for instance inference. -/
class PivotalCategory where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  tensorCoherenceIso : ∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ
  monoidality : ∀ (V W : C),
    (pivotalIso (V ⊗ W)).hom =
      ((pivotalIso V).hom ⊗ₘ (pivotalIso W).hom) ≫ (tensorCoherenceIso V W).hom
  dimUnit : leftQuantumTrace C (pivotalIso (𝟙_ C)).hom = 𝟙 (𝟙_ C)

section PivotalSection
variable [PivotalCategory C]

/-- Pivotal dimension of an object `V` in a pivotal category: the left quantum trace of
the pivotal isomorphism `V ≅ (Vᘁ)ᘁ`. -/
noncomputable def pivotalDimension (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace C (PivotalCategory.pivotalIso (C := C) V).hom

/-- Alias for `pivotalDimension`: the left quantum dimension of `V`. -/
noncomputable abbrev leftQuantumDim (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalDimension C V

/-- Alias for `pivotalDimension`: the categorical dimension of `V`. -/
noncomputable abbrev categoricalDimension (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalDimension C V

/-- Pivotal trace of an endomorphism `f : V ⟶ V`: the left quantum trace of `f` composed
with the pivotal isomorphism. -/
noncomputable def pivotalTrace {V : C} (f : V ⟶ V) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace C (f ≫ (PivotalCategory.pivotalIso (C := C) V).hom)

/-- Alias for `pivotalTrace`: the categorical trace of an endomorphism. -/
noncomputable def categoricalTrace {V : C} (f : V ⟶ V) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalTrace C f

/-- Multiplicativity of the left quantum trace on tensor products. -/
structure Proposition_1_37_1 : Prop where
  left_eq_right_dual : ∀ {V : C} (a : V ⟶ (Vᘁ)ᘁ),
    leftQuantumTrace C a =
      η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)
  additivity : ∀ [Preadditive C] [HasBinaryBiproducts C] {V W : C}
    (a : V ⟶ (Vᘁ)ᘁ) (b : W ⟶ (Wᘁ)ᘁ)
    (ψ : (Vᘁ)ᘁ ⊞ (Wᘁ)ᘁ ≅ ((Limits.biprod V W)ᘁ : C)ᘁ),
    leftQuantumTrace C (Limits.biprod.lift (Limits.biprod.fst ≫ a) (Limits.biprod.snd ≫ b) ≫ ψ.hom) =
      leftQuantumTrace C a + leftQuantumTrace C b
  multiplicativity : ∀ {V W : C}
    (a : V ⟶ (Vᘁ)ᘁ) (b : W ⟶ (Wᘁ)ᘁ)
    (φ : (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ),
    leftQuantumTrace C ((a ⊗ₘ b) ≫ φ.hom) =
      leftQuantumTrace C a ≫ leftQuantumTrace C b
  cyclicity_left : ∀ {V : C} (a : V ⟶ (Vᘁ)ᘁ) (c : V ⟶ V),
    leftQuantumTrace C (c ≫ a) = leftQuantumTrace C (a ≫ (cᘁ)ᘁ)
  cyclicity_right : ∀ {V : C} (a : V ⟶ ᘁ(ᘁV)) (c : V ⟶ V),
    rightQuantumTrace C (c ≫ a) =
      rightQuantumTrace C (a ≫ leftAdjointMate (leftAdjointMate c))

/-- EGNO Proposition 1.38.5: the pivotal dimension is a character of the Grothendieck
ring (multiplicative on tensor products, additive on biproducts, and sending the unit to
1). -/
structure Proposition_1_38_5_IsCharacter [Preadditive C] [HasBinaryBiproducts C] : Prop where
  multiplicativity : ∀ (V W : C), pivotalDimension C (V ⊗ W) =
    pivotalDimension C V ≫ pivotalDimension C W
  additivity : ∀ (X Y : C), pivotalDimension C (Limits.biprod X Y) =
    pivotalDimension C X + pivotalDimension C Y
  unitality : pivotalDimension C (𝟙_ C) = 𝟙 (𝟙_ C)

/-- EGNO Proposition 1.38.5 holds: the pivotal dimension is a character of the
Grothendieck ring. -/
end PivotalSection

/-- A spherical category is a pivotal category in which the pivotal dimension of every
object equals the pivotal dimension of its dual. -/
class SphericalCategory extends PivotalCategory C where
  spherical : ∀ (V : C), pivotalDimension C V = pivotalDimension C (Vᘁ)

/-- EGNO Definition 1.39.1: synonym for `SphericalCategory`. -/
abbrev def_1_39_1 := SphericalCategory C

section SphericalSection
variable [SphericalCategory C]

/-- Helper for the spherical-trace equality: in a spherical category, the pivotal trace of
an endomorphism can be expressed via the right-dual evaluation/coevaluation. -/
end SphericalSection

/-- EGNO Proposition 1.37.3: both left and right quantum traces are additive on short
exact sequences of objects compatible with the chosen morphisms to the double duals. -/
structure Proposition_1_37_3 : Prop where
  left_additive : ∀ [Preadditive C] {V W Q : C}
    (i : W ⟶ V) (p : V ⟶ Q)
    (aV : V ⟶ (Vᘁ)ᘁ) (aW : W ⟶ (Wᘁ)ᘁ) (aQ : Q ⟶ (Qᘁ)ᘁ)
    (_ : Mono i) (_ : Epi p)
    (_ : i ≫ p = 0)
    (_ : i ≫ aV = aW ≫ (iᘁ)ᘁ)
    (_ : p ≫ aQ = aV ≫ (pᘁ)ᘁ),
    leftQuantumTrace C aV = leftQuantumTrace C aW + leftQuantumTrace C aQ
  right_additive : ∀ [Preadditive C] {V W Q : C}
    (i : W ⟶ V) (p : V ⟶ Q)
    (aV : V ⟶ ᘁ(ᘁV)) (aW : W ⟶ ᘁ(ᘁW)) (aQ : Q ⟶ ᘁ(ᘁQ))
    (_ : Mono i) (_ : Epi p)
    (_ : i ≫ p = 0)
    (_ : i ≫ aV = aW ≫ leftAdjointMate (leftAdjointMate i))
    (_ : p ≫ aQ = aV ≫ leftAdjointMate (leftAdjointMate p)),
    rightQuantumTrace C aV = rightQuantumTrace C aW + rightQuantumTrace C aQ

/-- EGNO Proposition 1.37.3 holds: bundled proof of additivity of the left and right
quantum traces on short exact sequences. -/
end TensorCategories
