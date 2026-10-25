import Mathlib
import Abbrev.GroupCohomology_TateCohomology
import Lemma.Representation.EqIndBotMk
import Abbrev.GroupCohomology_TateDimensionShiftMaps

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

lemma indBotMap_comp_indBotπ {A B : Rep.{u} k G} (φ : A ⟶ B) : indBotMap φ ≫ indBotπ B = indBotπ A ≫ φ := by
  let adj := Rep.indResAdjunction k (⊥ : Subgroup G).subtype
  have hadj : ∀ (X : Rep.{u} k (⊥ : Subgroup G)) (Y : Rep.{u} k G) (f : Rep.ind (⊥ : Subgroup G).subtype X ⟶ Y),
      adj.homEquiv X Y f = Rep.indResHomEquiv (⊥ : Subgroup G).subtype X Y f := fun X Y f => rfl
  have hπ : ∀ (X : Rep.{u} k G), indBotπ X = (adj.homEquiv _ _).symm (𝟙 _) := fun X => by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, hadj]
    exact (Rep.indResHomEquiv (⊥ : Subgroup G).subtype ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj X) X).apply_symm_apply (𝟙 _)
  have e1 := adj.homEquiv_naturality_left_symm ((Rep.resFunctor (⊥ : Subgroup G).subtype).map φ)
    (𝟙 ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj B))
  have e2 := adj.homEquiv_naturality_right_symm (𝟙 ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A)) φ
  rw [Category.comp_id] at e1
  rw [Category.id_comp] at e2
  rw [hπ A, hπ B]
  exact e1.symm.trans e2

def dimShiftDownObjMap {A B : Rep.{u} k G} (φ : A ⟶ B) : A.dimShiftDownObj ⟶ B.dimShiftDownObj :=
  Rep.ofHom
    ⟨LinearMap.codRestrict _ ((indBotMap φ).hom.toLinearMap ∘ₗ (LinearMap.ker (indBotπ A).hom.toLinearMap).subtype)
        (fun x => by
          show (indBotπ B).hom ((indBotMap φ).hom (x : A.indBot)) = 0
          rw [← Rep.comp_apply, indBotMap_comp_indBotπ, Rep.comp_apply]
          have hx : (indBotπ A).hom (x : A.indBot) = 0 := x.2
          rw [hx, map_zero]),
      fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply (indBotMap φ) g (x : A.indBot))⟩

@[simp] lemma coe_dimShiftDownObjMap_apply {A B : Rep.{u} k G} (φ : A ⟶ B) (x : A.dimShiftDownObj) :
    ((dimShiftDownObjMap φ).hom x : B.indBot) = (indBotMap φ).hom (x : A.indBot) := rfl

def dimShiftDownMap {A B : Rep.{u} k G} (φ : A ⟶ B) : A.dimShiftDown ⟶ B.dimShiftDown where
  τ₁ := dimShiftDownObjMap φ
  τ₂ := indBotMap φ
  τ₃ := φ
  comm₁₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  comm₂₃ := indBotMap_comp_indBotπ φ

def indBotSC (X : ShortComplex (Rep.{u} k G)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (indBotMap X.f) (indBotMap X.g) (by
    show (Rep.indFunctor k (⊥ : Subgroup G).subtype).map ((Rep.resFunctor (⊥ : Subgroup G).subtype).map X.f)
        ≫ (Rep.indFunctor k (⊥ : Subgroup G).subtype).map ((Rep.resFunctor (⊥ : Subgroup G).subtype).map X.g) = 0
    rw [← Functor.map_comp, ← Functor.map_comp, X.zero, Functor.map_zero, Functor.map_zero])

def dimShiftDownSC (X : ShortComplex (Rep.{u} k G)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (dimShiftDownObjMap X.f) (dimShiftDownObjMap X.g) (by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Subtype.ext ?_))
    show (indBotMap X.g).hom ((indBotMap X.f).hom (x : X.X₁.indBot)) = 0
    rw [← Rep.comp_apply, show indBotMap X.f ≫ indBotMap X.g = 0 from (indBotSC X).zero]
    rfl)

def dimShiftDownSCι (X : ShortComplex (Rep.{u} k G)) : dimShiftDownSC X ⟶ indBotSC X where
  τ₁ := X.X₁.dimShiftDown.f
  τ₂ := X.X₂.dimShiftDown.f
  τ₃ := X.X₃.dimShiftDown.f
  comm₁₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  comm₂₃ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

def indBotSCπ (X : ShortComplex (Rep.{u} k G)) : indBotSC X ⟶ X where
  τ₁ := indBotπ X.X₁
  τ₂ := indBotπ X.X₂
  τ₃ := indBotπ X.X₃
  comm₁₂ := (indBotMap_comp_indBotπ X.f).symm
  comm₂₃ := (indBotMap_comp_indBotπ X.g).symm

end Rep

end
