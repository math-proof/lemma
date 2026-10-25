-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_IdealSheafHom.lean: instance decls only.
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Lemma.AlgebraicGeometry.IdealSheafHom

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData

namespace IdealHom

variable {I J K : X.IdealSheafData}

instance : Zero (IdealHom I J) := ⟨⟨fun _ => 0, fun h x => by simp⟩⟩
instance : Add (IdealHom I J) :=
  ⟨fun φ ψ => ⟨fun U => φ.app U + ψ.app U, fun h x => by
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add, φ.coe_app_resLE h x,
      ψ.coe_app_resLE h x]⟩⟩
instance : Neg (IdealHom I J) :=
  ⟨fun φ => ⟨fun U => -φ.app U, fun h x => by
    simp only [LinearMap.neg_apply, Submodule.coe_neg, map_neg, φ.coe_app_resLE h x]⟩⟩
instance : Sub (IdealHom I J) :=
  ⟨fun φ ψ => ⟨fun U => φ.app U - ψ.app U, fun h x => by
    simp only [LinearMap.sub_apply, Submodule.coe_sub, map_sub, φ.coe_app_resLE h x,
      ψ.coe_app_resLE h x]⟩⟩
instance : SMul ℕ (IdealHom I J) :=
  ⟨fun n φ => ⟨fun U => n • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, Submodule.coe_smul_of_tower, map_nsmul,
      φ.coe_app_resLE h x]⟩⟩
instance : SMul ℤ (IdealHom I J) :=
  ⟨fun n φ => ⟨fun U => n • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, Submodule.coe_smul_of_tower, map_zsmul,
      φ.coe_app_resLE h x]⟩⟩


instance : AddCommGroup (IdealHom I J) :=
  Function.Injective.addCommGroup (fun φ : IdealHom I J => φ.app)
    (fun _ _ h => ext h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : SMul Γ(X, ⊤) (IdealHom I J) :=
  ⟨fun s φ => ⟨fun U => sresTop U s • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, SetLike.val_smul, smul_eq_mul, map_mul,
      φ.coe_app_resLE h x, sres_sresTop]⟩⟩


instance : Module Γ(X, ⊤) (IdealHom I J) where
  one_smul φ := by ext U x; simp
  mul_smul r s φ := by ext U x; simp [mul_smul]
  smul_zero r := by ext U x; simp
  smul_add r φ ψ := by ext U x; simp
  add_smul r s φ := by ext U x; simp [add_smul]
  zero_smul φ := by ext U x; simp

end IdealHom

end IdealSheafData

end AlgebraicGeometry.Scheme
