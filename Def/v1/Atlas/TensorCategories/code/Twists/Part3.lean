/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
import Theorem.v1.Atlas.TensorCategories.code.Twists
open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


section GaugeEquiv

variable {R : Type u} [CommSemiring R]

variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- Auxiliary element `Q_J = m ∘ (S ⊗ id)(J)` used in defining the twisted antipode. -/
noncomputable def twistQ (J : H ⊗[R] H) : H :=
  LinearMap.mul' R H (TensorProduct.map (HopfAlgebra.antipode R) LinearMap.id J)

/-- Auxiliary element `Q_{J⁻¹} = m ∘ (id ⊗ S)(J⁻¹)` used in defining the twisted
antipode. -/
noncomputable def twistQInv (Jinv : H ⊗[R] H) : H :=
  LinearMap.mul' R H (TensorProduct.map LinearMap.id (HopfAlgebra.antipode R) Jinv)

/-- Twisted antipode of a Hopf algebra along a twist `J`: conjugation of `S(x)` by
the elements `Q_{J⁻¹}` and `Q_J`. -/
noncomputable def twistedAntipode (J : (H ⊗[R] H)ˣ) (x : H) : H :=
  twistQInv R H J.inv * HopfAlgebra.antipode R x * twistQ R H J.val

end BialgebraTwist


section TwistClasses

variable (R : Type u) [CommSemiring R]

variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- Setoid on bialgebra twists induced by gauge equivalence on the underlying
units. -/
noncomputable def gaugeEquivSetoid : Setoid (BialgebraTwist R H) where
  r T₁ T₂ := GaugeEquiv T₁.J T₂.J
  iseqv := {
    refl := fun T => GaugeEquiv.refl T.J
    symm := fun h => GaugeEquiv.symm h
    trans := fun h₁ h₂ => GaugeEquiv.trans h₁ h₂
  }

/-- Gauge-equivalence classes of bialgebra twists. -/
def BialgebraTwistClasses :=
  Quotient (gaugeEquivSetoid R H)

end TwistClasses

section FiberFunctorClasses

open TensorCategories CategoryTheory

universe v w

/-- Setoid on fiber functors: identify two functors if their underlying functors are
isomorphic. -/
noncomputable def fiberFunctorSetoid
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] :
    Setoid (FiberFunctor k C) where
  r F₁ F₂ := Nonempty (F₁.F ≅ F₂.F)
  iseqv := {
    refl := fun F => ⟨Iso.refl _⟩
    symm := fun ⟨i⟩ => ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩
  }

/-- Isomorphism classes of fiber functors on `C`. -/
def FiberFunctorIsoClasses
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] :=
  Quotient (fiberFunctorSetoid k C)

/-- Two fiber functors are monoidally isomorphic if there is an isomorphism of their
underlying functors that respects the monoidal structures. -/
def MonoidalFiberFunctorIsomorphic
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (F₁ F₂ : FiberFunctor k C) : Prop :=
  letI : F₁.F.LaxMonoidal := F₁.monoidal.toLaxMonoidal
  letI : F₂.F.LaxMonoidal := F₂.monoidal.toLaxMonoidal
  ∃ (e : F₁.F ≅ F₂.F), NatTrans.IsMonoidal e.hom

/-- Setoid on fiber functors quotienting by monoidal isomorphism. -/
noncomputable def monoidalFiberFunctorSetoid
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] :
    Setoid (FiberFunctor k C) where
  r := MonoidalFiberFunctorIsomorphic k C
  iseqv := {
    refl := fun F => by
      unfold MonoidalFiberFunctorIsomorphic
      letI : F.F.LaxMonoidal := F.monoidal.toLaxMonoidal
      refine ⟨Iso.refl _, ?_⟩
      show NatTrans.IsMonoidal (𝟙 F.F)
      infer_instance
    symm := fun {F₁ F₂} h => by
      unfold MonoidalFiberFunctorIsomorphic at h ⊢
      letI : F₁.F.LaxMonoidal := F₁.monoidal.toLaxMonoidal
      letI : F₂.F.LaxMonoidal := F₂.monoidal.toLaxMonoidal
      obtain ⟨e, he⟩ := h
      refine ⟨e.symm, ?_⟩
      show NatTrans.IsMonoidal e.inv
      infer_instance
    trans := fun {F₁ F₂ F₃} h₁ h₂ => by
      unfold MonoidalFiberFunctorIsomorphic at h₁ h₂ ⊢
      letI : F₁.F.LaxMonoidal := F₁.monoidal.toLaxMonoidal
      letI : F₂.F.LaxMonoidal := F₂.monoidal.toLaxMonoidal
      letI : F₃.F.LaxMonoidal := F₃.monoidal.toLaxMonoidal
      obtain ⟨e₁, he₁⟩ := h₁
      obtain ⟨e₂, he₂⟩ := h₂
      refine ⟨e₁.trans e₂, ?_⟩
      show NatTrans.IsMonoidal (e₁.hom ≫ e₂.hom)
      infer_instance
  }

/-- Monoidal-isomorphism classes of fiber functors on `C`. -/
def MonoidalFiberFunctorIsoClasses
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] :=
  Quotient (monoidalFiberFunctorSetoid k C)

end FiberFunctorClasses


/-- Opaque placeholder for the representation category `Rep(H)` of a bialgebra `H`. -/
opaque RepCat (k : Type u) [Field k] (H : Type u) [Ring H] [Algebra k H] [Bialgebra k H] :
    Type u := PUnit

