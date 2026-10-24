/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Products.Basic

set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


section CoalgebraRecap

variable (R : Type u) (A : Type v) [CommSemiring R] [AddCommMonoid A] [Module R A]
variable [Coalgebra R A]

example : A →ₗ[R] A ⊗[R] A := Coalgebra.comul

example : A →ₗ[R] R := Coalgebra.counit

example : TensorProduct.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul =
    comul.lTensor A ∘ₗ (comul : A →ₗ[R] A ⊗[R] A) :=
  Coalgebra.coassoc

example : counit.rTensor A ∘ₗ (comul : A →ₗ[R] A ⊗[R] A) = TensorProduct.mk R _ _ 1 :=
  Coalgebra.rTensor_counit_comp_comul

example : counit.lTensor A ∘ₗ (comul : A →ₗ[R] A ⊗[R] A) = (TensorProduct.mk R _ _).flip 1 :=
  Coalgebra.lTensor_counit_comp_comul

end CoalgebraRecap

abbrev Definition_1_20_1 (R : Type u) (C : Type v)
    [CommSemiring R] [AddCommMonoid C] [Module R C] :=
  Coalgebra R C

structure Subcoalgebra (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    extends Submodule R A where
  comul_mem : ∀ a ∈ toSubmodule,
    Coalgebra.comul a ∈ Submodule.map₂ (TensorProduct.mk R A A) toSubmodule toSubmodule

namespace Subcoalgebra

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

instance : SetLike (Subcoalgebra R A) A where
  coe S := S.toSubmodule
  coe_injective' S T h := by
    cases S; cases T; congr 1; exact SetLike.coe_injective h

end Subcoalgebra


class Comodule (R : Type u) (C : Type v) (M : Type*)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] where
  coact : M →ₗ[R] C ⊗[R] M
  coassoc : TensorProduct.assoc R C C M ∘ₗ Coalgebra.comul.rTensor M ∘ₗ coact =
    coact.lTensor C ∘ₗ coact
  counit_coact : Coalgebra.counit.rTensor M ∘ₗ coact = TensorProduct.mk R R M 1

abbrev LeftComodule_def_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  Comodule R C M

abbrev Definition_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  Comodule R C M

instance Coalgebra.regularComodule (R : Type u) (C : Type v)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    Comodule R C C where
  coact := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  counit_coact := Coalgebra.rTensor_counit_comp_comul

class RightComodule (R : Type u) (C : Type v) (M : Type*)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] where
  coact : M →ₗ[R] M ⊗[R] C
  coassoc : (TensorProduct.assoc R M C C) ∘ₗ coact.rTensor C ∘ₗ coact =
    Coalgebra.comul.lTensor M ∘ₗ coact
  counit_coact : Coalgebra.counit.lTensor M ∘ₗ coact = (TensorProduct.mk R M R).flip 1

abbrev RightComodule_def_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  RightComodule R C M

instance Coalgebra.regularRightComodule (R : Type u) (C : Type v)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    RightComodule R C C where
  coact := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  counit_coact := Coalgebra.lTensor_counit_comp_comul


section BialgebraRecap

variable (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Bialgebra R A]

example : Algebra R A := Bialgebra.toAlgebra
example : Coalgebra R A := Bialgebra.toCoalgebra

example : A →ₐ[R] A ⊗[R] A := Bialgebra.comulAlgHom R A

example : A →ₐ[R] R := Bialgebra.counitAlgHom R A

example (a b : A) : Coalgebra.comul (R := R) (a * b) =
    Coalgebra.comul a * Coalgebra.comul b :=
  Bialgebra.comul_mul a b

example (a b : A) : Coalgebra.counit (R := R) (a * b) =
    Coalgebra.counit a * Coalgebra.counit b :=
  Bialgebra.counit_mul a b

example : Coalgebra.comul (R := R) (1 : A) = 1 := Bialgebra.comul_one

example : Coalgebra.counit (R := R) (1 : A) = 1 := Bialgebra.counit_one

end BialgebraRecap


section Thm_1_21_1

open MonoidalCategory

variable (k : Type u) [CommRing k]
variable (C : Type v) [Category.{w} C] [MonoidalCategory C] [Preadditive C] [Linear k C]
variable (F : C ⥤ ModuleCat.{u} k) [F.Monoidal] [F.Faithful]

set_option synthInstance.maxHeartbeats 400000

/-- The counit `End(F) → k` of the bialgebra `End(F)` of a fiber functor `F`: evaluate the
natural transformation at the unit object and read off its action on `1 ∈ k`. -/
noncomputable def endF_counit_def : End F →ₗ[k] k where
  toFun η :=
    ((Functor.Monoidal.εIso F).hom ≫ η.app (𝟙_ C) ≫
      (Functor.Monoidal.εIso F).inv).hom (1 : k)
  map_add' η₁ η₂ := by
    have : (η₁ + η₂).app (𝟙_ C) = η₁.app (𝟙_ C) + η₂.app (𝟙_ C) := rfl
    simp only [this, Preadditive.add_comp, Preadditive.comp_add]
    rfl
  map_smul' r η := by
    have h1 : (r • η).app (𝟙_ C) = r • η.app (𝟙_ C) := rfl
    simp only [h1, RingHom.id_apply]
    suffices h : (Functor.Monoidal.εIso F).hom ≫ (r • η.app (𝟙_ C)) ≫
      (Functor.Monoidal.εIso F).inv =
      r • ((Functor.Monoidal.εIso F).hom ≫ η.app (𝟙_ C) ≫
        (Functor.Monoidal.εIso F).inv) by
      simp only [h]; rfl
    rw [show (r • η.app (𝟙_ C)) ≫ (Functor.Monoidal.εIso F).inv =
        r • (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv) from
        Linear.smul_comp _ _ _ _ _ _]
    rw [show (Functor.Monoidal.εIso F).hom ≫
        (r • (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv)) =
        r • ((Functor.Monoidal.εIso F).hom ≫
          (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv)) from
        Linear.comp_smul _ _ _ _ _ _]

/-- The bifunctor `(X, Y) ↦ F(X) ⊗ F(Y)` from `C × C` to `ModuleCat k`, used to express
the multiplicative structure on `End(F)`. -/
noncomputable def functorSelfTensor :
    (C × C) ⥤ ModuleCat.{u} k where
  obj XY := F.obj XY.1 ⊗ F.obj XY.2
  map f := F.map f.1 ⊗ₘ F.map f.2
  map_id XY := by
    change F.map (𝟙 XY.1) ⊗ₘ F.map (𝟙 XY.2) = 𝟙 _
    rw [F.map_id, F.map_id, id_tensorHom_id]
  map_comp f g := by
    change F.map (f.1 ≫ g.1) ⊗ₘ F.map (f.2 ≫ g.2) = _
    rw [F.map_comp, F.map_comp, tensorHom_comp_tensorHom]

/-- The tensor product `End(F) ⊗_k End(F)` is itself a (semi)ring via the tensor product
of algebras. -/
noncomputable instance instSemiringEndTensor :
    Semiring (TensorProduct k (End F) (End F)) :=
  Algebra.TensorProduct.instSemiring

/-- The tensor product `End(F) ⊗_k End(F)` is a `k`-algebra. -/
noncomputable instance instAlgebraEndTensor :
    Algebra k (TensorProduct k (End F) (End F)) :=
  Algebra.TensorProduct.instAlgebra

/-- Proposition 1.18.3: the canonical algebra isomorphism
`End(F₁) ⊗ End(F₂) ≅ End(F₁ ⊗ F₂)`, here specialized to `F₁ = F₂ = F`. -/
def evalAtHom (Z : C) : End F →ₗ[k] (↑(F.obj Z) →ₗ[k] ↑(F.obj Z)) where
  toFun η := (η.app Z).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Wrap a `k`-linear endomorphism of the underlying module into the corresponding
endomorphism in `ModuleCat k`. -/
def wrapEnd (M : ModuleCat.{u} k) : (↑M →ₗ[k] ↑M) →ₗ[k] End M where
  toFun f := ModuleCat.ofHom f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical map `End(F) ⊗ End(F) → End(F(X) ⊗ F(Y))` sending `η₁ ⊗ η₂` to
`η₁ ⊗ η₂` evaluated component-wise. -/
noncomputable def endF_tensor_hom (X Y : C) :
    (End F) ⊗[k] (End F) →ₗ[k] End (F.obj X ⊗ F.obj Y) :=
  (wrapEnd k (F.obj X ⊗ F.obj Y)) ∘ₗ
  (TensorProduct.homTensorHomMap (.id k) ↑(F.obj X) ↑(F.obj Y) ↑(F.obj X) ↑(F.obj Y)) ∘ₗ
  (TensorProduct.map (evalAtHom k C F X) (evalAtHom k C F Y))

/-- The coalgebra structure on `End(F)` arising from `endF_comul` and `endF_counit_def`. -/
def thm_1_21_1_converse (R' : Type*) (H' : Type*) [CommSemiring R'] [Semiring H']
    [Algebra R' H']
    (Δ : H' →ₐ[R'] H' ⊗[R'] H') (ε : H' →ₐ[R'] R')
    (h_coassoc : (Algebra.TensorProduct.assoc R' R' R' H' H' H').toAlgHom.comp
      ((Algebra.TensorProduct.map Δ (.id R' H')).comp Δ) =
      (Algebra.TensorProduct.map (.id R' H') Δ).comp Δ)
    (h_rTensor : (Algebra.TensorProduct.map ε (.id R' H')).comp Δ =
      (Algebra.TensorProduct.lid R' H').symm.toAlgHom)
    (h_lTensor : (Algebra.TensorProduct.map (.id R' H') ε).comp Δ =
      (Algebra.TensorProduct.rid R' R' H').symm.toAlgHom) :
    Bialgebra R' H' :=
  Bialgebra.ofAlgHom Δ ε h_coassoc h_rTensor h_lTensor

end Thm_1_21_1

section Def_1_21_2

/-- A bialgebra over `R` is an algebra equipped with a compatible coalgebra structure. -/
abbrev IsBialgebra (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] :=
  Bialgebra R H

/-- Definition 1.21.2: An algebra `H` with comultiplication `Δ` and counit `ε` satisfying
the bialgebra axioms is called a *bialgebra*. -/
abbrev Definition_1_21_2 (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] :=
  Bialgebra R H

end Def_1_21_2


section FundamentalTheorem

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]
