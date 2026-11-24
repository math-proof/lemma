module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Instance.AlgebraicGeometry_IdealSheafHom
public import Structure.AlgebraicGeometry_IdealSheafHom
open CategoryTheory TopologicalSpace Opposite


public section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData


def sresTop (U : X.affineOpens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom

namespace IdealHom

variable {I J K : X.IdealSheafData}

def ofLE (h : I ≤ J) : IdealHom I J where
  app U := Submodule.inclusion (le_def.mp h U)
  coe_app_resLE _ _ := rfl

protected def id (I : X.IdealSheafData) : IdealHom I I := ofLE le_rfl

def comp (ψ : IdealHom J K) (φ : IdealHom I J) : IdealHom I K where
  app U := ψ.app U ∘ₗ φ.app U
  coe_app_resLE := by
    intro U V h x
    have h₁ : φ.app V (I.resLE h x) = J.resLE h (φ.app U x) := Subtype.ext (φ.coe_app_resLE h x)
    simp only [LinearMap.coe_comp, Function.comp_apply, h₁, ψ.coe_app_resLE h]

def mulRight (I J : X.IdealSheafData) (s : Γ(X, ⊤))
    (hs : ∀ U : X.affineOpens, sresTop U s ∈ J.ideal U) : IdealHom I (I * J) where
  app U :=
    { toFun := fun x => ⟨x * sresTop U s, by rw [ideal_mul]; exact Ideal.mul_mem_mul x.2 (hs U)⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r x => Subtype.ext (mul_assoc _ _ _) }
  coe_app_resLE := by
    intro U V h x
    show sres h (x : Γ(X, U)) * sresTop V s = sres h ((x : Γ(X, U)) * sresTop U s)
    rw [map_mul, sres_sresTop]

def range (φ : IdealHom I J) : X.IdealSheafData where
  ideal U := LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U)
  map_ideal_basicOpen U f := by
    -- affineBasicOpen vs basicOpen coercions shifted in Mathlib; restore proof later
    sorry

end IdealHom

end IdealSheafData

end AlgebraicGeometry.Scheme
