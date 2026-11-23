module

public import Mathlib
public import Def.GroupCohomology_RepCokernel
public import Abbrev.GroupCohomology_RepImage

public section

set_option autoImplicit false

open CategoryTheory
open GroupCohomology.RepImage (obj)

namespace Rep.RepImage

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)


public theorem ι_hom_apply (y : obj f) : (ι f).hom y = (y : Y) := rfl


public theorem toImage_hom_apply_coe (x : X) : ((toImage f).hom x : Y) = f.hom x := rfl


public theorem toImage_ι : toImage f ≫ ι f = f := Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)


public theorem ι_hom_injective : Function.Injective (ι f).hom := Subtype.coe_injective


public theorem map_hom_apply_coe {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') (y : obj f) :
    ((map f f' α β w).hom y : Y') = β.hom (y : Y) := rfl


public theorem map_ι {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') :
    map f f' α β w ≫ ι f' = ι f ≫ β := Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

