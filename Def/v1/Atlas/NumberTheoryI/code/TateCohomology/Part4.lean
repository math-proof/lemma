/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Def.v1.Atlas.NumberTheoryI.code.Cor2328
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor2328
import Instance.v1.Atlas.NumberTheoryI.code.TateCohomology.Part3


noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

def tateH0.mk (A : Rep k G) : A.ρ.invariants →ₗ[k] tateH0 A :=
  Submodule.mkQ _

def tateMinus1.mk (A : Rep k G) : LinearMap.ker (normMap k G A) →ₗ[k] tateMinus1 A :=
  Submodule.mkQ _

def herbrandQuotient [IsCyclic G] (A : Rep k G)
    [Fintype (tateH0 A)] [Fintype (tateMinus1 A)] : ℚ :=
  (Fintype.card (tateH0 A) : ℚ) / (Fintype.card (tateMinus1 A) : ℚ)

def tateHnAux {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]
    (A : Rep k G) : Bool → Type u
  | true  => tateH0 A
  | false => tateMinus1 A

def parityBool (n : ℤ) : Bool := n % 2 == 0

def tateHn (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G]
    [IsCyclic G] (A : Rep k G) (n : ℤ) : Type u :=
  tateHnAux A (parityBool n)


def tateMinus1_ind_augRetract {k : Type u} [CommRing k] {G : Type u} [Group G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    Representation.IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] ↑B := by
  apply Representation.Coinvariants.lift _
    (TensorProduct.lift ((LinearMap.lsmul k (↑B : Type u)) ∘ₗ
      Finsupp.linearCombination k (fun (_ : G) => (1 : k))))
  intro g
  have : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
  subst this
  rw [map_one]
  exact LinearMap.comp_id _


def tateMinus1_ind_proj1 {k : Type u} [CommRing k] {G : Type u} [Group G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    Representation.IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] ↑B := by
  apply Representation.Coinvariants.lift _
    (TensorProduct.lift ((LinearMap.lsmul k (↑B : Type u)) ∘ₗ
      (Finsupp.lapply (1 : G))))
  intro g
  have : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
  subst this
  rw [map_one]
  exact LinearMap.comp_id _

def HerbrandMultiplicative [IsCyclic G] (S : ShortComplex (Rep k G)) : Prop :=
  ∀ (i₁ : Fintype (tateH0 S.X₁)) (i₂ : Fintype (tateMinus1 S.X₁))
    (i₃ : Fintype (tateH0 S.X₂)) (i₄ : Fintype (tateMinus1 S.X₂))
    (i₅ : Fintype (tateH0 S.X₃)) (i₆ : Fintype (tateMinus1 S.X₃)),
    @herbrandQuotient _ _ _ _ _ _ S.X₂ i₃ i₄ =
      @herbrandQuotient _ _ _ _ _ _ S.X₁ i₁ i₂ *
      @herbrandQuotient _ _ _ _ _ _ S.X₃ i₅ i₆

def invEquivTrivInt {G₀ : Type} [Group G₀] [Fintype G₀] :
    (Rep.trivial ℤ G₀ ℤ).ρ.invariants ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofEq _ _ (by ext x; simp [Representation.mem_invariants])).trans
    Submodule.topEquiv

end TateCohomology
end
