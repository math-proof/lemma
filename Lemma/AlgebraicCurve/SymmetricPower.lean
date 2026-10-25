import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Structure.AlgebraicCurve_SymmetricPower

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)


namespace finFibrePow


theorem proj_comp (l : Fin r) : proj c r l ≫ c = toBase c r :=
  WidePullback.π_arrow _ _


theorem permAct_hom (σ : Equiv.Perm (Fin r)) : (permAct c r σ).hom = permHom c r σ := rfl

theorem permAct_inv (σ : Equiv.Perm (Fin r)) : (permAct c r σ).inv = permHom c r σ⁻¹ := rfl

@[reassoc]
theorem permAct_hom_proj (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (permAct c r σ).hom ≫ proj c r (σ i) = proj c r i := by
  rw [permAct_hom, permHom_proj, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

@[reassoc]
theorem permAct_hom_toBase (σ : Equiv.Perm (Fin r)) :
    (permAct c r σ).hom ≫ toBase c r = toBase c r := by
  rw [permAct_hom, permHom_toBase]

end finFibrePow


end AlgebraicGeometry

namespace AlgebraicCurve

open AlgebraicGeometry


end AlgebraicCurve
