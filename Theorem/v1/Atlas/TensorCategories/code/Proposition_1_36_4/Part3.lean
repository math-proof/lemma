/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Def.v1.Atlas.TensorCategories.code.Proposition_1_36_4.Part3
open scoped TensorProduct
open CategoryTheory

universe u


section Prop1364FiberFunctorClasses

open TensorCategories

universe v w

/-- Monoidal isomorphism of fiber functors is reflexive. -/
theorem Prop1364.FiberFunctorMonoidalIsomorphic.refl
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (FF : FiberFunctor k C) : Prop1364.FiberFunctorMonoidalIsomorphic FF FF :=
  ⟨Iso.refl _, @NatTrans.IsMonoidal.id C _ _ (ModuleCat k) _ _ FF.F FF.monoidal.toLaxMonoidal⟩

/-- Monoidal isomorphism of fiber functors is symmetric. -/
theorem Prop1364.FiberFunctorMonoidalIsomorphic.symm
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    {FF₁ FF₂ : FiberFunctor k C}
    (h : Prop1364.FiberFunctorMonoidalIsomorphic FF₁ FF₂) :
    Prop1364.FiberFunctorMonoidalIsomorphic FF₂ FF₁ := by
  obtain ⟨α, hα⟩ := h
  exact ⟨α.symm, isMonoidal_inv_of_isMonoidal_hom α hα⟩

/-- Monoidal isomorphism of fiber functors is transitive. -/
theorem Prop1364.FiberFunctorMonoidalIsomorphic.trans
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    {FF₁ FF₂ FF₃ : FiberFunctor k C}
    (h₁₂ : Prop1364.FiberFunctorMonoidalIsomorphic FF₁ FF₂)
    (h₂₃ : Prop1364.FiberFunctorMonoidalIsomorphic FF₂ FF₃) :
    Prop1364.FiberFunctorMonoidalIsomorphic FF₁ FF₃ := by
  obtain ⟨α, hα⟩ := h₁₂
  obtain ⟨β, hβ⟩ := h₂₃
  exact ⟨α.trans β, isMonoidal_comp_of_isMonoidal α.hom β.hom hα hβ⟩

/-- Monoidal isomorphism of fiber functors is an equivalence relation. -/
theorem Prop1364.FiberFunctorMonoidalIsomorphic.equivalence
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] :
    Equivalence (Prop1364.FiberFunctorMonoidalIsomorphic (k := k) (C := C)) where
  refl := Prop1364.FiberFunctorMonoidalIsomorphic.refl
  symm := Prop1364.FiberFunctorMonoidalIsomorphic.symm
  trans := Prop1364.FiberFunctorMonoidalIsomorphic.trans

end Prop1364FiberFunctorClasses
