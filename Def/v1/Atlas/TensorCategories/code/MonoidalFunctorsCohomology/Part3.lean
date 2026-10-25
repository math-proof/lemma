/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Mathlib.GroupTheory.GroupAction.Basic
import Theorem.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part2
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section Cohomology

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- Two 2-cochains are cohomologous if they differ by a coboundary `d¹η`. -/
def Cohomologous2 (μ₁ μ₂ : Cochain2 G A) : Prop :=
  ∃ η : Cochain1 G A, ∀ g h : G, μ₂ g h = μ₁ g h * d1 G A η g h

/-- Two 3-cochains are cohomologous if they differ by a coboundary `d²μ`. -/
def Cohomologous3 (ω₁ ω₂ : Cochain3' G A) : Prop :=
  ∃ μ : Cochain2 G A, ∀ g h l : G, ω₂ g h l = ω₁ g h l * d2 G A μ g h l

/-- The equivalence relation on 2-cochains given by being cohomologous, packaged as a
`Setoid`. -/
def cohomologous2Setoid : Setoid (Cochain2 G A) where
  r := Cohomologous2 G A
  iseqv := {
    refl := fun μ => ⟨fun _ => 1, fun g h => by simp [d1]⟩
    symm := fun {μ₁ μ₂} ⟨η, hη⟩ =>
      ⟨fun g => (η g)⁻¹, fun g h => by
        have := hη g h
        rw [this, d1_inv, mul_inv_cancel_right]⟩
    trans := fun {μ₁ μ₂ μ₃} ⟨η₁, h₁⟩ ⟨η₂, h₂⟩ =>
      ⟨fun g => η₁ g * η₂ g, fun g h => by
        rw [h₂ g h, h₁ g h]; simp [d1, mul_assoc, mul_comm, mul_left_comm]⟩
  }

/-- The equivalence relation on 3-cochains given by being cohomologous, packaged as a
`Setoid`. -/
def cohomologous3Setoid : Setoid (Cochain3' G A) where
  r := Cohomologous3 G A
  iseqv := {
    refl := fun ω => ⟨fun _ _ => 1, fun g h l => by simp [d2]⟩
    symm := fun {ω₁ ω₂} ⟨μ, hμ⟩ =>
      ⟨fun g h => (μ g h)⁻¹, fun g h l => by
        have := hμ g h l
        rw [this, d2_inv, mul_inv_cancel_right]⟩
    trans := fun {ω₁ ω₂ ω₃} ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩ =>
      ⟨fun g h => μ₁ g h * μ₂ g h, fun g h l => by
        rw [h₂ g h l, h₁ g h l]; simp [d2, mul_assoc, mul_comm, mul_left_comm]⟩
  }

/-- The second group cohomology `H²(G, A)` realised as the quotient of 2-cochains by the
cohomologous relation. -/
def H2 := Quotient (cohomologous2Setoid G A)

/-- The third group cohomology `H³(G, A)` realised as the quotient of 3-cochains by the
cohomologous relation. -/
def H3 := Quotient (cohomologous3Setoid G A)

end Cohomology

section MonoidalStructureFromCocycle

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

end MonoidalStructureFromCocycle

section MonoidalFunctors

variable (G₁ : Type u) [Group G₁] (G₂ : Type u) [Group G₂]

variable (A : Type v) [CommGroup A]

/-- The pullback of a 3-cochain on `G₂` along a group homomorphism `f : G₁ →* G₂`. -/
def pullback3 (f : G₁ →* G₂) (ω : Cochain3' G₂ A) : Cochain3' G₁ A :=
  fun g h l => ω (f g) (f h) (f l)

/-- The compatibility condition relating the 2-cochain data `μ` of a monoidal functor to
the source and target 3-cocycles, expressing the hexagon-type axiom of EGNO §1.7. -/
def IsMonoidalFunctorData (ω₁ : Cochain3' G₁ A) (ω₂ : Cochain3' G₂ A)
    (f : G₁ →* G₂) (μ : Cochain2 G₁ A) : Prop :=
  ∀ g h l : G₁,
    ω₁ g h l * μ h l * μ g (h * l) = ω₂ (f g) (f h) (f l) * μ g h * μ (g * h) l

/-- The compatibility condition `η(g) η(h) μ(g,h) = μ'(g,h) η(gh)` on a 1-cochain `η`
relating two 2-cochains `μ` and `μ'`; this is the condition that `η` is a monoidal natural
transformation between the corresponding monoidal structures. -/
def IsMonoidalNatTransData (μ μ' : Cochain2 G A) (η : Cochain1 G A) : Prop :=
  ∀ g h : G, η g * η h * μ g h = μ' g h * η (g * h)

/-- A monoidal natural isomorphism is monoidal natural transformation data `η` together
with a pointwise inverse 1-cochain `η_inv`. -/
def IsMonoidalNatIso (μ μ' : Cochain2 G A) (η : Cochain1 G A) : Prop :=
  IsMonoidalNatTransData G A μ μ' η ∧
  ∃ η_inv : Cochain1 G A, ∀ g : G, η g * η_inv g = 1 ∧ η_inv g * η g = 1

/-- Repackage a 3-cocycle as a `GroupCocycle3`, the structure consumed by the
`GradedVec` machinery to produce a monoidal structure on graded vector spaces. -/
def groupCocycle3_of_isCocycle3 (ω : Cochain3' G A) (h : IsCocycle3 G A ω) :
    GroupCocycle3 G A where
  toFun := ω
  cocycle_cond := (isCocycle3_iff_cocycleCond G A ω).mp h

end MonoidalFunctors
