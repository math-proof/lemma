module

public import Mathlib
public import Def.GroupCohomology_RepCokernel
public import Abbrev.GroupCohomology_RepImage

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open GroupCohomology.RepImage (obj)

namespace Rep.RepImage

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable def ι : obj f ⟶ Y := Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

noncomputable def toImage : X ⟶ obj f :=
  Rep.ofHom ⟨LinearMap.rangeRestrict f.hom.toLinearMap, fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply f g x)⟩

noncomputable def map {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') : obj f ⟶ obj f' :=
  Rep.ofHom ⟨LinearMap.codRestrict _ (β.hom.toLinearMap ∘ₗ Submodule.subtype _) (by
      rintro ⟨_, x, rfl⟩
      refine ⟨α.hom x, ?_⟩
      change f'.hom (α.hom x) = β.hom (f.hom x)
      have := congrArg (fun φ : X ⟶ Y' => φ.hom x) w
      exact this.symm),
    fun g => LinearMap.ext fun y => Subtype.ext (Rep.hom_comm_apply β g (y : Y))⟩

noncomputable def seq : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (ι f) (GroupCohomology.RepCokernel.π f)
    (Rep.hom_ext (DFunLike.ext _ _ fun y => (GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff f _).2 y.2))

end Rep.RepImage

end
