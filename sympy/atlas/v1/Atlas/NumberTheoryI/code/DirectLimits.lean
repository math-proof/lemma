/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirectLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Constructions
import Mathlib.Order.Directed

namespace TopologicalSpace.DirectLimit

section BasicDefs

variable {ι : Type*} [Preorder ι]
  (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (f : ∀ i j, i ≤ j → X i → X j)

def Rel : (Σ i, X i) → (Σ i, X i) → Prop :=
  fun a b => ∃ (i j : ι) (h : i ≤ j) (x : X i),
    a = ⟨i, x⟩ ∧ b = ⟨j, f i j h x⟩

def directLimitSetoid : Setoid (Σ i, X i) :=
  Relation.EqvGen.setoid (Rel X f)

end BasicDefs

abbrev Space {ι : Type*} [Preorder ι]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (f : ∀ i j, i ≤ j → X i → X j) : Type _ :=
  @Quotient (Σ i, X i) (directLimitSetoid X f)

section Maps

variable {ι : Type*} [Preorder ι]
  (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (f : ∀ i j, i ≤ j → X i → X j)

def of (i : ι) (x : X i) : Space X f :=
  @Quotient.mk' _ (directLimitSetoid X f) ⟨i, x⟩

noncomputable def lift {Y : Type*} [TopologicalSpace Y]
    (ψ : ∀ i, X i → Y)
    (hψ_comp : ∀ i j (h : i ≤ j) (x : X i), ψ j (f i j h x) = ψ i x) :
    Space X f → Y :=
  @Quotient.lift _ _ (directLimitSetoid X f) (fun σ => ψ σ.1 σ.2) <| by
    intro a b hab
    change ψ a.1 a.2 = ψ b.1 b.2
    induction hab with
    | rel a b hr =>
      obtain ⟨i, j, h, x, rfl, rfl⟩ := hr
      exact (hψ_comp i j h x).symm
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
