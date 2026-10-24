/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiBialgebra

open scoped TensorProduct
open CategoryTheory

universe u


section MonoidalNatTransHelpers

variable {C : Type*} [Category C] [MonoidalCategory C]
  {D : Type*} [Category D] [MonoidalCategory D]
  {F G H : C ⥤ D}

/-- Helper: the inverse of a monoidal natural isomorphism is again monoidal. -/
lemma isMonoidal_inv_of_isMonoidal_hom
    {lmF : F.LaxMonoidal} {lmG : G.LaxMonoidal}
    (α : F ≅ G)
    (hα : @NatTrans.IsMonoidal _ _ _ _ _ _ F G α.hom lmF lmG) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ G F α.inv lmG lmF := by
  letI := lmF; letI := lmG; letI := hα; exact inferInstance

/-- Helper: the composition of monoidal natural transformations is monoidal. -/
lemma isMonoidal_comp_of_isMonoidal
    {lmF : F.LaxMonoidal} {lmG : G.LaxMonoidal} {lmH : H.LaxMonoidal}
    (α : F ⟶ G) (β : G ⟶ H)
    (hα : @NatTrans.IsMonoidal _ _ _ _ _ _ F G α lmF lmG)
    (hβ : @NatTrans.IsMonoidal _ _ _ _ _ _ G H β lmG lmH) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ F H (α ≫ β) lmF lmH := by
  letI := lmF; letI := lmG; letI := lmH; letI := hα; letI := hβ
  exact NatTrans.IsMonoidal.comp α β

end MonoidalNatTransHelpers


namespace Prop1364

variable (R : Type u) [CommSemiring R]
variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- The algebra map `(ε ⊗ id) : H ⊗ H → H` used to express normalization of a bialgebra
twist. -/
noncomputable def counitTensorId :
    H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.lid R H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R H) (AlgHom.id R H))

/-- The algebra map `(id ⊗ ε) : H ⊗ H → H` used to express normalization of a bialgebra
twist. -/
noncomputable def idTensorCounit :
    H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.rid R R H).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R H))

/-- The algebra map `(id ⊗ Δ) : H ⊗ H → H ⊗ (H ⊗ H)` used in the cocycle equation. -/
noncomputable def idTensorComul :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.comulAlgHom R H)

/-- The algebra map `(Δ ⊗ id) : H ⊗ H → H ⊗ (H ⊗ H)` (using the associator) used in the
cocycle equation. -/
noncomputable def comulTensorId :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H))

/-- The algebra inclusion `H ⊗ H ↪ H ⊗ (H ⊗ H)` sending `x ⊗ y ↦ 1 ⊗ (x ⊗ y)`, appearing as
`(1 ⊗ J)` in the cocycle equation. -/
noncomputable def embedRight :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.includeRight

/-- The algebra inclusion `H ⊗ H ↪ H ⊗ (H ⊗ H)` sending `x ⊗ y ↦ (x ⊗ y) ⊗ 1`, appearing as
`(J ⊗ 1)` in the cocycle equation. -/
noncomputable def embedLeft :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    Algebra.TensorProduct.includeLeft

end Prop1364


/-- A bialgebra twist (Definition 1.36.1): an invertible element `J ∈ H ⊗ H` satisfying
the normalization conditions and the twist (cocycle) equation. -/
structure Prop1364.BialgebraTwist (R : Type u) [CommSemiring R]
    (H : Type u) [Semiring H] [Bialgebra R H] where
  J : (H ⊗[R] H)ˣ
  left_norm : Prop1364.counitTensorId R H J.val = 1
  right_norm : Prop1364.idTensorCounit R H J.val = 1
  cocycle :
    Prop1364.idTensorComul R H J.val * Prop1364.embedRight R H J.val
    = Prop1364.comulTensorId R H J.val * Prop1364.embedLeft R H J.val


section Prop1364GaugeEquiv

variable {R : Type u} [CommSemiring R]
variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- Gauge equivalence on bialgebra twists: `J₁ ~ J₂` iff there is a unit `v ∈ Hˣ` with
`J₂ = Δ(v) · J₁ · (v⁻¹ ⊗ v⁻¹)`. -/
def Prop1364.GaugeEquiv (J₁ J₂ : (H ⊗[R] H)ˣ) : Prop :=
  ∃ v : Hˣ, (J₂ : H ⊗[R] H) = Bialgebra.comulAlgHom R H (v : H) *
    (J₁ : H ⊗[R] H) * ((↑v⁻¹ : H) ⊗ₜ[R] (↑v⁻¹ : H))

/-- Gauge equivalence of bialgebra twists is reflexive (witnessed by `v = 1`). -/
theorem Prop1364.GaugeEquiv.refl (J : (H ⊗[R] H)ˣ) : Prop1364.GaugeEquiv J J := by
  refine ⟨1, ?_⟩
  simp [Units.val_one, map_one, one_mul, inv_one, ← Algebra.TensorProduct.one_def, mul_one]

/-- Gauge equivalence of bialgebra twists is symmetric. -/
theorem Prop1364.GaugeEquiv.symm {J₁ J₂ : (H ⊗[R] H)ˣ}
    (h : Prop1364.GaugeEquiv J₁ J₂) :
    Prop1364.GaugeEquiv J₂ J₁ := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v⁻¹, ?_⟩
  simp only [inv_inv]
  rw [hv]
  have hΔ : (Bialgebra.comulAlgHom R H) ↑v⁻¹ * (Bialgebra.comulAlgHom R H) ↑v = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have htmul : ((↑v⁻¹ : H) ⊗ₜ[R] (↑v⁻¹ : H)) * ((↑v : H) ⊗ₜ[R] (↑v : H)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp [Units.inv_mul, Algebra.TensorProduct.one_def]
  rw [mul_assoc, mul_assoc, mul_assoc, htmul, mul_one]
  rw [← mul_assoc ((Bialgebra.comulAlgHom R H) ↑v⁻¹), hΔ, one_mul]

/-- Gauge equivalence of bialgebra twists is transitive. -/
theorem Prop1364.GaugeEquiv.trans {J₁ J₂ J₃ : (H ⊗[R] H)ˣ}
    (h₁₂ : Prop1364.GaugeEquiv J₁ J₂) (h₂₃ : Prop1364.GaugeEquiv J₂ J₃) :
    Prop1364.GaugeEquiv J₁ J₃ := by
  obtain ⟨v₁, hv₁⟩ := h₁₂
  obtain ⟨v₂, hv₂⟩ := h₂₃
  refine ⟨v₂ * v₁, ?_⟩
  rw [hv₂, hv₁]
  simp only [Units.val_mul, map_mul, mul_inv_rev]
  rw [← Algebra.TensorProduct.tmul_mul_tmul]
  simp only [mul_assoc]

/-- The setoid on `BialgebraTwist R H` given by gauge equivalence. -/
noncomputable def Prop1364.gaugeEquivSetoid :
    Setoid (Prop1364.BialgebraTwist R H) where
  r T₁ T₂ := Prop1364.GaugeEquiv T₁.J T₂.J
  iseqv := {
    refl := fun T => Prop1364.GaugeEquiv.refl T.J
    symm := fun h => Prop1364.GaugeEquiv.symm h
    trans := fun h₁ h₂ => Prop1364.GaugeEquiv.trans h₁ h₂
  }

/-- The set of gauge equivalence classes of bialgebra twists on `H`. -/
def Prop1364.BialgebraTwistClasses :=
  Quotient (Prop1364.gaugeEquivSetoid R H)

end Prop1364Classes


section Prop1364FiberFunctorClasses

open TensorCategories

universe v w

/-- Two fiber functors are monoidally isomorphic if there exists a natural isomorphism
between their underlying functors which is also a monoidal natural transformation. -/
def Prop1364.FiberFunctorMonoidalIsomorphic
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (FF₁ FF₂ : FiberFunctor k C) : Prop :=
  ∃ (α : FF₁.F ≅ FF₂.F),
    @NatTrans.IsMonoidal C _ _ (ModuleCat k) _ _ FF₁.F FF₂.F α.hom
      FF₁.monoidal.toLaxMonoidal FF₂.monoidal.toLaxMonoidal

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

/-- Setoid on `FiberFunctor k C` given by monoidal isomorphism. -/
noncomputable def Prop1364.fiberFunctorSetoid
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] :
    Setoid (FiberFunctor k C) where
  r := Prop1364.FiberFunctorMonoidalIsomorphic
  iseqv := Prop1364.FiberFunctorMonoidalIsomorphic.equivalence

/-- The set of monoidal isomorphism classes of fiber functors on `C`. -/
def Prop1364.FiberFunctorIsoClasses
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] :=
  Quotient (Prop1364.fiberFunctorSetoid k C)

end Prop1364FiberFunctorClasses


/-- The category of finite-dimensional representations of a bialgebra `H` over `k`. -/
