module

public import Def.AlgebraicGeometry_RelEffCartierDiv

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)

variable {f r} in

noncomputable def functor : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Σ g : unop T ⟶ S, RelEffCartierDiv f r g
  map φ := TypeCat.ofHom fun D => ⟨φ.unop ≫ D.1, D.2.pullbackAlong φ.unop rfl⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun D => ?_
    obtain ⟨g, D⟩ := D
    change (⟨𝟙 _ ≫ g, D.pullbackAlong (𝟙 _) rfl⟩ : Σ g : unop T ⟶ S, RelEffCartierDiv f r g) = ⟨g, D⟩
    exact Sigma.ext (Category.id_comp g)
      ((D.pullbackAlong_heq (𝟙 _) rfl (Category.id_comp g)).trans (heq_of_eq D.pullbackAlong_id))
  map_comp {T T' T''} φ ψ := by
    refine ConcreteCategory.hom_ext _ _ fun D => ?_
    obtain ⟨g, D⟩ := D
    change (⟨(ψ.unop ≫ φ.unop) ≫ g, D.pullbackAlong (ψ.unop ≫ φ.unop) rfl⟩ :
        Σ g : unop T'' ⟶ S, RelEffCartierDiv f r g) =
      ⟨ψ.unop ≫ φ.unop ≫ g, (D.pullbackAlong φ.unop rfl).pullbackAlong ψ.unop rfl⟩
    exact Sigma.ext (Category.assoc _ _ _)
      ((D.pullbackAlong_heq (ψ.unop ≫ φ.unop) rfl (Category.assoc _ _ _)).trans
        (heq_of_eq (D.pullbackAlong_comp φ.unop rfl ψ.unop rfl).symm))

variable {f r}

def IsUniversal {Y : Scheme.{u}} {y : Y ⟶ S} (Duniv : RelEffCartierDiv f r y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (D : RelEffCartierDiv f r g),
    ∃! φ : {φ : T ⟶ Y // φ ≫ y = g}, PullsBackOver Duniv φ.1 φ.2 D

section Representability

variable {Y : Scheme.{u}} {y : Y ⟶ S}

variable {Duniv : RelEffCartierDiv f r y}

noncomputable def IsUniversal.lift (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) : T ⟶ Y :=
  (hU g D).exists.choose.1

noncomputable def IsUniversal.homEquiv (hU : Duniv.IsUniversal) (T : Scheme.{u}) :
    (T ⟶ Y) ≃ Σ g : T ⟶ S, RelEffCartierDiv f r g where
  toFun φ := ⟨φ ≫ y, Duniv.pullbackAlong φ rfl⟩
  invFun D := hU.lift D.2
  left_inv φ := hU.lift_pullbackAlong φ
  right_inv D := Sigma.ext (hU.lift_comp D.2)
    ((Duniv.pullbackAlong_heq _ rfl (hU.lift_comp D.2)).trans (heq_of_eq (hU.pullbackAlong_lift D.2)))

noncomputable def IsUniversal.representableBy (hU : Duniv.IsUniversal) :
    (RelEffCartierDiv.functor f r).RepresentableBy Y where
  homEquiv {T} := hU.homEquiv T
  homEquiv_comp {T T'} φ ψ := by
    change (⟨(φ ≫ ψ) ≫ y, Duniv.pullbackAlong (φ ≫ ψ) rfl⟩ : Σ g : T ⟶ S, RelEffCartierDiv f r g) =
      ⟨φ ≫ ψ ≫ y, (Duniv.pullbackAlong ψ rfl).pullbackAlong φ rfl⟩
    exact Sigma.ext (Category.assoc _ _ _)
      ((Duniv.pullbackAlong_heq (φ ≫ ψ) rfl (Category.assoc _ _ _)).trans
        (heq_of_eq (Duniv.pullbackAlong_comp ψ rfl φ rfl).symm))


end Representability

end RelEffCartierDiv

end AlgebraicGeometry

end
