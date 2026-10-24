import Mathlib
import Lemma.Definitions.Def_GroupCohomology_RepCokernel

set_option autoImplicit false

open CategoryTheory

namespace GroupCohomology.RepImage

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable abbrev obj : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨x, rfl⟩
    exact ⟨X.ρ g x, Rep.hom_comm_apply f g x⟩)

noncomputable def ι : obj f ⟶ Y := Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

theorem ι_hom_apply (y : obj f) : (ι f).hom y = (y : Y) := rfl

noncomputable def toImage : X ⟶ obj f :=
  Rep.ofHom ⟨LinearMap.rangeRestrict f.hom.toLinearMap, fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply f g x)⟩

theorem toImage_hom_apply_coe (x : X) : ((toImage f).hom x : Y) = f.hom x := rfl

theorem toImage_ι : toImage f ≫ ι f = f := Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

theorem ι_hom_injective : Function.Injective (ι f).hom := Subtype.coe_injective

noncomputable def map {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') : obj f ⟶ obj f' :=
  Rep.ofHom ⟨LinearMap.codRestrict _ (β.hom.toLinearMap ∘ₗ Submodule.subtype _) (by
      rintro ⟨_, x, rfl⟩
      refine ⟨α.hom x, ?_⟩
      change f'.hom (α.hom x) = β.hom (f.hom x)
      have := congrArg (fun φ : X ⟶ Y' => φ.hom x) w
      exact this.symm),
    fun g => LinearMap.ext fun y => Subtype.ext (Rep.hom_comm_apply β g (y : Y))⟩

theorem map_hom_apply_coe {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') (y : obj f) :
    ((map f f' α β w).hom y : Y') = β.hom (y : Y) := rfl

theorem map_ι {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') :
    map f f' α β w ≫ ι f' = ι f ≫ β := Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

noncomputable def seq : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (ι f) (GroupCohomology.RepCokernel.π f)
    (Rep.hom_ext (DFunLike.ext _ _ fun y => (GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff f _).2 y.2))

end GroupCohomology.RepImage
