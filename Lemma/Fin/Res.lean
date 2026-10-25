import sympy.Basic
import Lemma.AlgebraicGeometry.OrderedAffineCoverCech
open CategoryTheory Opposite
set_option autoImplicit false


noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)

@[reducible] def moduleRestrict {U U' : V.Opens} (h : U ≤ U') :
  Module (V.presheaf.obj (op U')) (F.obj U) :=
  Module.compHom (F.obj U) (V.presheaf.map (homOfLE h).op).hom

def Res {U U' : V.Opens} (h : U ≤ U') :
  let := F.moduleRestrict h
  F.obj U' →ₗ[V.presheaf.obj (op U')] F.obj U :=
  let := F.moduleRestrict h
  { toFun := F.res h
    map_add' := map_add _
    map_smul' := fun a x => F.res_smul h a x }


/--
[res_apply]
-/
@[path]
private lemma main
-- given
  {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') :
-- imply
  Res (F := F) h x = F.res h x := by
-- proof
  rfl

end AlgebraicGeometry.OModulePresheaf

end


-- created on 2026-10-24
