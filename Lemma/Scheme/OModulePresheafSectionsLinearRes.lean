import Lemma.AlgebraicGeometry.OrderedAffineCoverCech
import Lemma.Fin.Res

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)

-- moduleRestrict / Res (was resₗ) / resₗ_apply extracted to Lemma.Fin.Res

theorem moduleRestrict_smul_def {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : F.obj U) :
    letI := F.moduleRestrict h
    a • x = (V.presheaf.map (homOfLE h).op).hom a • x := rfl

end AlgebraicGeometry.OModulePresheaf

end
