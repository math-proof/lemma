import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Lemma.AlgebraicGeometry.TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)

def ofModules : OModulePresheaf π where
  obj U := Γ(M, U)
  addCommGroup _ := inferInstance
  module U := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
  moduleSections _ := inferInstance
  isScalarTower U := Scheme.TwoAffineOpenCover.isScalarTower_sections π M U
  res h := Scheme.TwoAffineOpenCover.restrictSections π M h
  res_smul h a x := Scheme.Modules.map_smul M (homOfLE h) a x
  res_refl U := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    refine LinearMap.ext fun x => ?_
    show M.presheaf.map (homOfLE (le_refl U)).op x = x
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), M.presheaf.map_id]
    rfl
  res_comp {U U' U''} h h' := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U''
    refine LinearMap.ext fun x => ?_
    show M.presheaf.map (homOfLE (h.trans h')).op x
      = M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE h').op x)
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

end AlgebraicGeometry.OModulePresheaf

end
