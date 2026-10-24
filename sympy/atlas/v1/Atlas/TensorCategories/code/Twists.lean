/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiBialgebra
import sympy.atlas.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology

open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


namespace BialgebraTwist

variable (R : Type u) [CommSemiring R]
variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- The algebra map `(ε ⊗ id) : H ⊗ H → H` collapsing the first tensor factor via
the counit. -/
noncomputable def counitTensorId :
    H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.lid R H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R H) (AlgHom.id R H))

/-- The algebra map `(id ⊗ ε) : H ⊗ H → H` collapsing the second tensor factor via
the counit. -/
noncomputable def idTensorCounit :
    H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.rid R R H).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R H))

/-- The algebra map `(id ⊗ Δ) : H ⊗ H → H ⊗ (H ⊗ H)` applying the comultiplication
to the second tensor factor. -/
noncomputable def idTensorComul :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.comulAlgHom R H)

/-- The algebra map `(Δ ⊗ id) : H ⊗ H → H ⊗ (H ⊗ H)` applying the comultiplication
to the first tensor factor, followed by the associator. -/
noncomputable def comulTensorId :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H))

/-- Right embedding `H ⊗ H → H ⊗ (H ⊗ H)` as `1 ⊗ (-)`. -/
noncomputable def embedRight :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.includeRight

/-- Left embedding `H ⊗ H → H ⊗ (H ⊗ H)` as `(-) ⊗ 1` followed by the associator. -/
noncomputable def embedLeft :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    Algebra.TensorProduct.includeLeft

end BialgebraTwist


section TwistDef

variable (R : Type u) [CommSemiring R]
variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- A bialgebra twist of `H`: a unit `J ∈ (H ⊗ H)ˣ` satisfying the counit
normalization conditions `(ε ⊗ id)(J) = 1`, `(id ⊗ ε)(J) = 1`, and the
cocycle identity. -/
structure BialgebraTwist where
  J : (H ⊗[R] H)ˣ
  left_norm : BialgebraTwist.counitTensorId R H J.val = 1
  right_norm : BialgebraTwist.idTensorCounit R H J.val = 1
  cocycle :
    BialgebraTwist.idTensorComul R H J.val * BialgebraTwist.embedRight R H J.val
    = BialgebraTwist.comulTensorId R H J.val * BialgebraTwist.embedLeft R H J.val

end TwistDef


section IsBialgebraTwistDef

variable (R : Type u) [CommSemiring R]
variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- The twisted associator built from `J` and `J⁻¹` using the four maps `embedRight`,
`idTensorComul`, `comulTensorId`, `embedLeft`. -/
noncomputable def BialgebraTwist.twistedAssociator
    (J : (H ⊗[R] H)ˣ) : H ⊗[R] (H ⊗[R] H) :=
  BialgebraTwist.embedRight R H (↑J⁻¹ : H ⊗[R] H) *
  BialgebraTwist.idTensorComul R H (↑J⁻¹ : H ⊗[R] H) *
  BialgebraTwist.comulTensorId R H (↑J : H ⊗[R] H) *
  BialgebraTwist.embedLeft R H (↑J : H ⊗[R] H)

/-- Predicate characterizing when `J ∈ (H ⊗ H)ˣ` is a bialgebra twist: counit
normalization and trivial twisted associator. -/
def IsBialgebraTwist (J : (H ⊗[R] H)ˣ) : Prop :=

  BialgebraTwist.counitTensorId R H J.val = 1 ∧
  BialgebraTwist.idTensorCounit R H J.val = 1 ∧

  BialgebraTwist.twistedAssociator R H J = 1

end IsBialgebraTwistDef


namespace BialgebraTwist

variable {R : Type u} [CommSemiring R]
variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- Twisted comultiplication of `H` along a bialgebra twist `T`: `Δ_T(x) = J⁻¹ Δ(x) J`. -/
noncomputable def twistedComul (T : BialgebraTwist R H) (x : H) : H ⊗[R] H :=
  ↑T.J⁻¹ * Bialgebra.comulAlgHom R H x * ↑T.J

end BialgebraTwist


section GaugeEquiv

variable {R : Type u} [CommSemiring R]
variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- Gauge equivalence of twists: `J₁ ∼ J₂` iff there is a unit `v ∈ Hˣ` with
`J₂ = Δ(v) · J₁ · (v⁻¹ ⊗ v⁻¹)`. -/
def GaugeEquiv (J₁ J₂ : (H ⊗[R] H)ˣ) : Prop :=
  ∃ v : Hˣ, (J₂ : H ⊗[R] H) = Bialgebra.comulAlgHom R H (v : H) *
    (J₁ : H ⊗[R] H) * ((↑v⁻¹ : H) ⊗ₜ[R] (↑v⁻¹ : H))

/-- Reflexivity of gauge equivalence of twists, witnessed by `v = 1`. -/
theorem GaugeEquiv.refl (J : (H ⊗[R] H)ˣ) : GaugeEquiv J J := by
  refine ⟨1, ?_⟩
  simp [Units.val_one, map_one, one_mul, inv_one, ← Algebra.TensorProduct.one_def, mul_one]

/-- Symmetry of gauge equivalence: inverting the witnessing unit `v`. -/
theorem GaugeEquiv.symm {J₁ J₂ : (H ⊗[R] H)ˣ} (h : GaugeEquiv J₁ J₂) :
    GaugeEquiv J₂ J₁ := by
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

/-- Transitivity of gauge equivalence: composing the witnessing units. -/
theorem GaugeEquiv.trans {J₁ J₂ J₃ : (H ⊗[R] H)ˣ}
    (h₁₂ : GaugeEquiv J₁ J₂) (h₂₃ : GaugeEquiv J₂ J₃) :
    GaugeEquiv J₁ J₃ := by
  obtain ⟨v₁, hv₁⟩ := h₁₂
  obtain ⟨v₂, hv₂⟩ := h₂₃
  refine ⟨v₂ * v₁, ?_⟩
  rw [hv₂, hv₁]
  simp only [Units.val_mul, map_mul, mul_inv_rev]
  rw [← Algebra.TensorProduct.tmul_mul_tmul]
  simp only [mul_assoc]

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

/-- Placeholder category instance on `RepCat k H`. -/
section Def_1_34_6

open scoped TensorProduct

universe v₁

variable (R : Type u) [CommSemiring R]
variable (H : Type v₁) [Semiring H] [Algebra R H]
variable [qb : QuasiBialgebra R H]

/-- Alias for Definition 1.34.6: a twist of a quasi-bialgebra. -/
abbrev Definition_1_34_6_QuasiBialgebraTwist := QuasiBialgebraTwist R H

/-- Alias for Definition 1.34.6: the twisted comultiplication associated to a
quasi-bialgebra twist. -/
noncomputable abbrev Definition_1_34_6_twistedComul
    (tw : QuasiBialgebraTwist R H) (x : H) : H ⊗[R] H :=
  tw.twistedComul x

/-- Alias for Definition 1.34.6: the twisted associator associated to a quasi-bialgebra
twist. -/
noncomputable abbrev Definition_1_34_6_twistedAssociator
    (tw : QuasiBialgebraTwist R H) : H ⊗[R] (H ⊗[R] H) :=
  tw.twistedAssociator

/-- New quasi-bialgebra structure on `H` obtained by twisting an existing one along a
twist `tw`. -/
end Def_1_34_6


section Def_1_34_2

/-- Alias for Definition 1.34.2: twist-equivalence of quasi-fiber functors. -/
abbrev Definition_1_34_2_TwistEquivalent := @QuasiFiberFunctor.TwistEquivalent

end Def_1_34_2


section QuasiHopfTwist

open scoped TensorProduct

universe v

variable {R : Type u} [CommSemiring R]
variable {H : Type v} [Semiring H] [Algebra R H]
variable [qh : QuasiHopfAlgebra R H]

/-- Twisted `α`-element of a quasi-Hopf algebra under a twist `tw`. -/
noncomputable def QuasiBialgebraTwist.twistedAlpha
    (tw : QuasiBialgebraTwist R H) : H :=
  QuasiBialgebra.sAlphaMap R H qh.S.toLinearMap qh.α_elem (tw.J : H ⊗[R] H)

/-- Twisted `β`-element of a quasi-Hopf algebra under a twist `tw`. -/
noncomputable def QuasiBialgebraTwist.twistedBeta
    (tw : QuasiBialgebraTwist R H) : H :=
  QuasiBialgebra.betaSMap R H qh.S.toLinearMap qh.β_elem (↑tw.J⁻¹ : H ⊗[R] H)

/-- New quasi-Hopf algebra structure on `H` obtained by twisting an existing one along
a twist `tw`. -/
end QuasiHopfTwist


section Thm_1_35_6

open TensorCategories CategoryTheory

/-- Opaque placeholder for the representation category `Rep(H)` of a quasi-Hopf
algebra `H`. -/
opaque QuasiRepCat (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] : Type u := PUnit

/-- Placeholder category instance on `QuasiRepCat k H`. -/
end Thm_1_35_6

/-- Alias for `thm_1_35_6_reconstruction` (Theorem 1.35.6 reconstruction). -/
section DrinfeldTwist

/-- Drinfeld twist theorem: every finite-dimensional quasi-bialgebra admits a twist
trivializing its associator (so it becomes an honest bialgebra after twisting). -/
end DrinfeldTwist


section CocycleH2

universe uu vv
variable (G : Type uu) [Group G] (A : Type vv) [CommGroup A]

/-- The set of group 2-cocycles `G × G → A`. -/
def Cocycle2 := { μ : Cochain2 G A // IsCocycle2 G A μ }

/-- Setoid on 2-cocycles induced by cohomologousness (differing by a coboundary). -/
def cocycleCohomologousSetoid : Setoid (Cocycle2 G A) where
  r μ₁ μ₂ := Cohomologous2 G A μ₁.val μ₂.val
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

/-- The second group cohomology `H²(G, A)`: cohomology classes of 2-cocycles. -/
def CocycleH2 := Quotient (cocycleCohomologousSetoid G A)

end CocycleH2

/-- Construction of a fiber functor on `Vec_G` from a 2-cocycle `G × G → k×`. -/
section TwistMonoidalEquiv

open CategoryTheory

/-- Bundled monoidal equivalence between monoidal categories taking instance
parameters explicitly: an equivalence whose functors in both directions are
monoidal and whose adjunction unit/counit are monoidal natural transformations. -/
structure MonoidalEquiv
    (C : Type*) (D : Type*)
    (instCatC : Category C) (instMonC : @MonoidalCategory C instCatC)
    (instCatD : Category D) (instMonD : @MonoidalCategory D instCatD) where
  equiv : @Equivalence C D instCatC instCatD
  functorMonoidal : @Functor.Monoidal C instCatC instMonC D instCatD instMonD equiv.functor
  inverseMonoidal : @Functor.Monoidal D instCatD instMonD C instCatC instMonC equiv.inverse
  isMonoidal : @Equivalence.IsMonoidal C instCatC instMonC D instCatD instMonD
    equiv functorMonoidal inverseMonoidal

/-- Representation category of the twisted quasi-Hopf algebra `H^{tw}` obtained from
`H` by a twist `tw`. -/
end TwistMonoidalEquiv
