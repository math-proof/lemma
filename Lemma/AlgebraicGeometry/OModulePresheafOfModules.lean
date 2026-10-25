import Lemma.AlgebraicGeometry.OrderedAffineCoverCech
import Lemma.AlgebraicGeometry.TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Def.AlgebraicGeometry_OModulePresheafOfModules

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)


theorem ofModules_obj (U : V.Opens) : (ofModules π M).obj U = Γ(M, U) := rfl

theorem ofModules_res_apply {U U' : V.Opens} (h : U ≤ U') (x : Γ(M, U')) :
    (ofModules π M).res h (show (ofModules π M).obj U' from x) = M.presheaf.map (homOfLE h).op x :=
  rfl

theorem ofModules_smul (U : V.Opens) (a : Γ(V, U)) (x : Γ(M, U)) :
    (show (ofModules π M).obj U from a • x) = a • (show (ofModules π M).obj U from x) := rfl

theorem ofModules_algebraMap_smul (U : V.Opens) (r : R) (x : (ofModules π M).obj U) :
    r • x = (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r • x :=
  rfl

theorem ofModules_twoChartSections (𝒱 : V.TwoAffineOpenCover) :
    (ofModules π M).twoChartSections 𝒱 = 𝒱.sectionsOf π M := rfl

end AlgebraicGeometry.OModulePresheaf

end
