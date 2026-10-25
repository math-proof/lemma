-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayBicomplex.lean: instance decls only.
import Mathlib
import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Instance.AlgebraicGeometry_OrderedAffineCoverOf
import Lemma.AlgebraicGeometry.OModulePresheafLerayBicomplex

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.OModulePresheaf.Leray

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits


section LerayDC

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

instance biC_abGrp (a b : ℕ) :
    AddCommGroup (biC p πZ K K' a b) :=
  inferInstanceAs (AddCommGroup (∀ στ : BiIdx K K' a b,
    (OModulePresheaf.unit (p ≫ πZ)).obj (biOpen p K K' a b στ.1 στ.2)))

instance biC_module (a b : ℕ) :
    Module R (biC p πZ K K' a b) :=
  inferInstanceAs (Module R (∀ στ : BiIdx K K' a b,
    (OModulePresheaf.unit (p ≫ πZ)).obj (biOpen p K K' a b στ.1 στ.2)))

end LerayDC

section RelAlt

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K' : Scheme.OrderedAffineCover V')

instance relAltC_modΓ (U : Z.Opens) (b : ℕ) :
    Module Γ(Z, U) (relAltC p πZ K' U b) :=
  @Pi.module _ _ _ _ _ fun τ => (pullOpen p πZ (K'.inter τ)).moduleSections U

instance relAltC_scalarTower (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
    IsScalarTower R Γ(Z, U) (relAltC p πZ K' U b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
  exact ⟨fun r a f => funext fun τ =>
    ((pullOpen p πZ (K'.inter τ)).isScalarTower U).smul_assoc
      r a (f τ)⟩

instance ker_relAltd_smul (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    SMul Γ(Z, U) ↥(LinearMap.ker (relAltd p πZ K' U b)) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  ⟨fun a x => ⟨a • x.1, LinearMap.mem_ker.mpr <| by
    rw [relAltd_Γsmul, LinearMap.mem_ker.mp x.2, smul_zero]⟩⟩

instance ker_relAltd_modΓ (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    Module Γ(Z, U) ↥(LinearMap.ker (relAltd p πZ K' U b)) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  Function.Injective.module Γ(Z, U) ⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩
    Subtype.val_injective (fun _ _ => rfl)

instance relAltH_smul (U : Z.Opens) (b : ℕ) :
    SMul Γ(Z, U) (relAltH p πZ K' U b) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  ⟨fun a => Quotient.map' (a • ·) fun x y h => (Submodule.quotientRel_def _).mpr <| by
    show a • x - a • y ∈ _
    rw [show a • x - a • y = a • (x - y) from Subtype.ext (smul_sub a x.1 y.1).symm]
    exact relAltHB_Γsmul p πZ K' U b a (x - y)
      ((Submodule.quotientRel_def _).mp h)⟩

instance relAltH_modΓ (U : Z.Opens) (b : ℕ) :
    Module Γ(Z, U) (relAltH p πZ K' U b) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  Function.Surjective.module Γ(Z, U)
    ⟨⟨Submodule.Quotient.mk, rfl⟩, fun _ _ => rfl⟩
    (Submodule.Quotient.mk_surjective _) (fun _ _ => rfl)

instance relAltH_scalarTower (U : Z.Opens) (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
    IsScalarTower R Γ(Z, U) (relAltH p πZ K' U b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections πZ U
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine ⟨fun r a => Quotient.ind' fun x => congrArg Submodule.Quotient.mk
    (Subtype.ext ?_)⟩
  exact (relAltC_scalarTower p πZ K' U b).smul_assoc r a x.1

end RelAlt


end AlgebraicGeometry.OModulePresheaf.Leray

end
