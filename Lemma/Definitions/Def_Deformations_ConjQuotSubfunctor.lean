import Mathlib
import Lemma.Definitions.Def_Deformations_TraceAlgebra

set_option autoImplicit false

universe u

open CategoryTheory Function IsLocalRing

namespace Deformation

section ConjQuot

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

open ProartinianCat

variable (n) in

noncomputable def conjQuotSubfunctor (F : Subfunctor (repnFunctor n G 𝓞)) :
    Subfunctor (repnQuotFunctor n G 𝓞) where
  obj R := (toRepnQuot n G 𝓞).app R '' F.obj R
  map {R S} f := by
    rintro _ ⟨ρ', hρ', rfl⟩
    exact ⟨(repnFunctor n G 𝓞).map f ρ', F.map f hρ', rfl⟩

variable (n) in

lemma mem_conjQuotSubfunctor_obj_iff {F : Subfunctor (repnFunctor n G 𝓞)}
    {R : ProartinianCat 𝓞} (q : (repnQuotFunctor n G 𝓞).obj R) :
    q ∈ (conjQuotSubfunctor n F).obj R ↔
      ∃ ρ' ∈ F.obj R, (Quotient.mk'' ρ' : (repnQuotFunctor n G 𝓞).obj R) = q := by
  constructor
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨ρ', hρ', rfl⟩
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨ρ', hρ', rfl⟩

variable (n) in

lemma mk_mem_conjQuotSubfunctor_obj {F : Subfunctor (repnFunctor n G 𝓞)}
    {R : ProartinianCat 𝓞} {ρ' : G →ₜ* GL n R} (hρ' : ρ' ∈ F.obj R) :
    (Quotient.mk'' ρ' : (repnQuotFunctor n G 𝓞).obj R) ∈ (conjQuotSubfunctor n F).obj R :=
  ⟨ρ', hρ', rfl⟩

variable (n) in

lemma conjQuotSubfunctor_mono {F F' : Subfunctor (repnFunctor n G 𝓞)} (h : F ≤ F') :
    conjQuotSubfunctor n F ≤ conjQuotSubfunctor n F' := by
  rintro R _ ⟨ρ', hρ', rfl⟩
  exact ⟨ρ', h _ hρ', rfl⟩

variable (n) in

noncomputable def condLiftToDeformation (F : Subfunctor (repnFunctor n G 𝓞)) :
    F.toFunctor ⟶ (conjQuotSubfunctor n F).toFunctor where
  app R := TypeCat.ofHom
    fun ρ' => ⟨Quotient.mk'' ρ'.1, mk_mem_conjQuotSubfunctor_obj n ρ'.2⟩
  naturality R S f := by
    ext ρ'
    rfl

variable (n) in

lemma condLiftToDeformation_surjective (F : Subfunctor (repnFunctor n G 𝓞))
    (R : ProartinianCat 𝓞) :
    Function.Surjective ((condLiftToDeformation n F).app R) := by
  rintro ⟨q, hq⟩
  obtain ⟨ρ', hρ', hq'⟩ := (mem_conjQuotSubfunctor_obj_iff n q).mp hq
  exact ⟨⟨ρ', hρ'⟩, Subtype.ext hq'⟩

end ConjQuot

section Assembly

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

open ProartinianCat

variable (n) in

def ConjStable (F : Subfunctor (repnFunctor n G 𝓞)) : Prop :=
  ∀ {A : ProartinianCat 𝓞} {ρ' : G →ₜ* GL n A}, ρ' ∈ F.obj A →
    ∀ {γ : ConjAct (GL n A)}, γ ∈ conjKer (n := n) A → γ • ρ' ∈ F.obj A

variable (n) in

def ReflectedByInjective (F : Subfunctor (repnFunctor n G 𝓞)) : Prop :=
  ∀ {T A : ProartinianCat 𝓞} (ι : T ⟶ A), Function.Injective ι.hom →
    ∀ {σ : G →ₜ* GL n T}, (repnFunctor n G 𝓞).map ι σ ∈ F.obj A → σ ∈ F.obj T

end Assembly

end Deformation
