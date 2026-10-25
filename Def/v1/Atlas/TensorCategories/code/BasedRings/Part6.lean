/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Instance.v1.Atlas.TensorCategories.code.BasedRings.Part2
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The group of outer automorphisms `Out(G) = MulAut G / Inn(G)`. -/
def OuterAut (G : Type*) [Group G] := MulAut G ⧸ InnerAutSubgroup G

/-- Pullback of a normalized 3-cocycle along a group automorphism `φ : G ≃* G`. -/
def cocyclePullback {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (φ : G ≃* G) (ω : NormalizedGroupCocycle3 G A) : NormalizedGroupCocycle3 G A where
  toFun a b c := ω.toFun (φ a) (φ b) (φ c)
  cocycle_cond g₁ g₂ g₃ g₄ := by
    simp only [map_mul]; exact ω.cocycle_cond (φ g₁) (φ g₂) (φ g₃) (φ g₄)
  normalized g h := by
    simp only [map_one]; exact ω.normalized (φ g) (φ h)

/-- Two normalized 3-cocycles are equivalent under the joint action of `MulAut G` and the
group of coboundaries (i.e. they have the same orbit in `H³(G, A)/Out(G)`). -/
def CocycleOutOrbitEquiv {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (ω₁ ω₂ : NormalizedGroupCocycle3 G A) : Prop :=
  ∃ (φ : G ≃* G), CocycleCohomologous (cocyclePullback φ ω₁) ω₂

end FusionRing
