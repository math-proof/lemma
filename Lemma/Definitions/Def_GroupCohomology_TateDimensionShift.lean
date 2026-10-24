import Mathlib
import Lemma.Definitions.Def_GroupCohomology_TateCohomology

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

section DimShift

variable {k G : Type u} [CommRing k] [Group G]

abbrev indBot (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.ind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A)

def indBotMk (A : Rep.{u} k G) (g : G) : A →ₗ[k] A.indBot :=
  Representation.IndV.mk (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A).ρ g

lemma indBotMk_apply (A : Rep.{u} k G) (g : G) (a : A) :
    A.indBotMk g a = Representation.IndV.mk (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A).ρ g a := rfl

def indBotπ (A : Rep.{u} k G) : A.indBot ⟶ A :=
  (Rep.indResHomEquiv (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A) A).symm (𝟙 _)

def indBotσ (A : Rep.{u} k G) : A →ₗ[k] A.indBot := A.indBotMk 1

def indBotr (A : Rep.{u} k G) : A.indBot →ₗ[k] A :=
  Representation.Coinvariants.lift _ (TensorProduct.lift ((LinearMap.lsmul k A).comp
      ((Finsupp.lapply 1).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)))
    (fun s => by rw [Subsingleton.elim s 1, map_one]; rfl)

abbrev dimShiftDownObj (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation A.indBot.ρ (LinearMap.ker (indBotπ A).hom.toLinearMap) fun g x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hx ⊢
    rw [Rep.hom_comm_apply, hx, map_zero])

def dimShiftDown (A : Rep.{u} k G) : ShortComplex (Rep.{u} k G) where
  X₁ := A.dimShiftDownObj
  X₂ := A.indBot
  X₃ := A
  f := Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩
  g := indBotπ A
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))

variable [Fintype G]

open scoped Classical in

def indBotι (A : Rep.{u} k G) : A ⟶ A.indBot :=
  (Rep.resIndAdjunction k (⊥ : Subgroup G)).unit.app A

abbrev dimShiftUpObj (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.quotient A.indBot.ρ (LinearMap.range (indBotι A).hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨A.ρ g a, Rep.hom_comm_apply (indBotι A) g a⟩)

def dimShiftUp (A : Rep.{u} k G) : ShortComplex (Rep.{u} k G) where
  X₁ := A
  X₂ := A.indBot
  X₃ := A.dimShiftUpObj
  f := indBotι A
  g := Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩))

end DimShift

end Rep

end
