import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Instance.AlgebraicGeometry_IdealSheafHom
import Structure.AlgebraicGeometry_IdealSheafHom

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData


def sresTop (U : X.affineOpens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom

lemma sres_apply {U V : X.affineOpens} (h : V ≤ U) (s : Γ(X, U)) :
    sres h s = (X.presheaf.map (homOfLE (show (V : X.Opens) ≤ U from h)).op).hom s := rfl

lemma sresTop_apply (U : X.affineOpens) (s : Γ(X, ⊤)) :
    sresTop U s = (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom s := rfl

@[simp] lemma sres_sresTop {U V : X.affineOpens} (h : V ≤ U) (s : Γ(X, ⊤)) :
    sres h (sresTop U s) = sresTop V s := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← X.presheaf.map_comp]; rfl

@[simp] lemma sres_sres {U V W : X.affineOpens} (h : W ≤ V) (h' : V ≤ U) (s : Γ(X, U)) :
    sres h (sres h' s) = sres (h.trans h') s := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← X.presheaf.map_comp]; rfl


@[simp] lemma coe_resLE (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U)
    (x : I.ideal U) : (I.resLE h x : Γ(X, V)) = sres h (x : Γ(X, U)) := rfl


namespace IdealHom

variable {I J K : X.IdealSheafData}

@[ext]
lemma ext {φ ψ : IdealHom I J} (h : φ.app = ψ.app) : φ = ψ := by
  cases φ; cases ψ; congr

@[simp] lemma zero_app (U : X.affineOpens) : (0 : IdealHom I J).app U = 0 := rfl
@[simp] lemma add_app (φ ψ : IdealHom I J) (U : X.affineOpens) :
    (φ + ψ).app U = φ.app U + ψ.app U := rfl
@[simp] lemma neg_app (φ : IdealHom I J) (U : X.affineOpens) : (-φ).app U = -φ.app U := rfl
@[simp] lemma sub_app (φ ψ : IdealHom I J) (U : X.affineOpens) :
    (φ - ψ).app U = φ.app U - ψ.app U := rfl
@[simp] lemma nsmul_app (n : ℕ) (φ : IdealHom I J) (U : X.affineOpens) :
    (n • φ).app U = n • φ.app U := rfl
@[simp] lemma zsmul_app (n : ℤ) (φ : IdealHom I J) (U : X.affineOpens) :
    (n • φ).app U = n • φ.app U := rfl


@[simp] lemma smul_app (s : Γ(X, ⊤)) (φ : IdealHom I J) (U : X.affineOpens) :
    (s • φ).app U = sresTop U s • φ.app U := rfl


def ofLE (h : I ≤ J) : IdealHom I J where
  app U := Submodule.inclusion (le_def.mp h U)
  coe_app_resLE _ _ := rfl

@[simp] lemma coe_ofLE_app (h : I ≤ J) (U : X.affineOpens) (x : I.ideal U) :
    ((ofLE h).app U x : Γ(X, U)) = x := rfl

protected def id (I : X.IdealSheafData) : IdealHom I I := ofLE le_rfl

@[simp] lemma id_app (I : X.IdealSheafData) (U : X.affineOpens) (x : I.ideal U) :
    (IdealHom.id I).app U x = x := rfl

def comp (ψ : IdealHom J K) (φ : IdealHom I J) : IdealHom I K where
  app U := ψ.app U ∘ₗ φ.app U
  coe_app_resLE := by
    intro U V h x
    have h₁ : φ.app V (I.resLE h x) = J.resLE h (φ.app U x) := Subtype.ext (φ.coe_app_resLE h x)
    simp only [LinearMap.coe_comp, Function.comp_apply, h₁, ψ.coe_app_resLE h]

@[simp] lemma comp_app (ψ : IdealHom J K) (φ : IdealHom I J) (U : X.affineOpens)
    (x : I.ideal U) : (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

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

@[simp] lemma coe_mulRight_app (I J : X.IdealSheafData) (s : Γ(X, ⊤))
    (hs : ∀ U : X.affineOpens, sresTop U s ∈ J.ideal U) (U : X.affineOpens) (x : I.ideal U) :
    ((mulRight I J s hs).app U x : Γ(X, U)) = x * sresTop U s :=
  rfl

def range (φ : IdealHom I J) : X.IdealSheafData where
  ideal U := LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U)
  map_ideal_basicOpen U f := by
    -- affineBasicOpen vs basicOpen coercions shifted in Mathlib; restore proof later
    sorry

@[simp] lemma ideal_range (φ : IdealHom I J) (U : X.affineOpens) :
    φ.range.ideal U = LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U) := rfl

lemma range_le (φ : IdealHom I J) : φ.range ≤ J := fun U => by
  rintro _ ⟨x, rfl⟩; exact (φ.app U x).2

end IdealHom

end IdealSheafData

end AlgebraicGeometry.Scheme
