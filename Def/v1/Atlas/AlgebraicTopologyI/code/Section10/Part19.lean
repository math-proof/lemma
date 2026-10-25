/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section10.Part12
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

/-- The basepoint of `X / A`: the image in `QuotientSpace X A` of any point `a ∈ A`. -/
def quotientBasepoint {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (_ : a ∈ A) : QuotientSpace X A :=
  Quotient.mk (collapseSetoid A) a

/-- The pointed pair `(X / A, [a])` where `[a]` is the collapsed image of `A`. -/
def quotientPair {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (ha : a ∈ A) : TopPair where
  space := QuotientSpace X A
  instTop := inferInstance
  sub := {quotientBasepoint A ha}

/-- The quotient map of pairs `(X, A) → (X/A, *)` sending each point to its equivalence class. -/
def collapseMapOfPairs {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (ha : a ∈ A) :
    MapOfPairs ⟨X, inferInstance, A⟩ (quotientPair A ha) where
  toFun := Quotient.mk (collapseSetoid A)
  continuous_toFun := continuous_quotient_mk'
  mapsTo := fun _ hx => Quotient.sound (Or.inr ⟨hx, ha⟩)

/-- The pair `(B, A ∩ B)` viewed inside `B` via the subtype inclusion `↥B ↪ X`. -/
def subspacePair {X : Type u} [TopologicalSpace X] (A B : Set X) : TopPair where
  space := ↥B
  instTop := inferInstance
  sub := Subtype.val ⁻¹' A

/-- The pair map `(B, A ∩ B) → (X, A)` given by the subtype inclusion `↥B ↪ X`. -/
def pairInclusion {X : Type u} [TopologicalSpace X] (A B : Set X) :
    MapOfPairs (subspacePair A B) ⟨X, inferInstance, A⟩ where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ hx => hx

variable {X : Type u} [TopologicalSpace X]

/-- Identification of `(B, A ∩ B)` with the excised pair `(X ∖ Bᶜ, A ∖ Bᶜ)` in the forward
direction. -/
def subspacePairToExcisePair (A B : Set X) :
    MapOfPairs (subspacePair A B)
      ((⟨X, inferInstance, A⟩ : TopPair).excisePair Bᶜ) where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [compl_compl]; exact hx⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun ⟨_, _⟩ hxA => hxA

/-- Identification of the excised pair `(X ∖ Bᶜ, A ∖ Bᶜ)` with `(B, A ∩ B)` in the reverse
direction. Inverse to `subspacePairToExcisePair`. -/
def excisePairToSubspacePair (A B : Set X) :
    MapOfPairs ((⟨X, inferInstance, A⟩ : TopPair).excisePair Bᶜ)
      (subspacePair A B) where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rwa [compl_compl] at hx⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun ⟨_, _⟩ hxA => hxA

/-- The homology map `H_n(B, A ∩ B) → H_n(X/A, *)` induced by the composition
"include into `(X, A)` then collapse `A`". This is the factorization used to deduce
that the collapse map induces an isomorphism on homology (Corollary 10.3). -/
def collapseFactorization
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X)
    {a : X} (ha : a ∈ A)
    (_hClosure : closure A ⊆ interior B) (_hDR : IsSubspaceDeformationRetract A B) :
    h.H n (subspacePair A B) →+ h.H n (quotientPair A ha) :=
  h.map n ((collapseMapOfPairs A ha).comp (pairInclusion A B))

end BrouwerFixedPoint
