import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData

def sres {U V : X.affineOpens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE (show (V : X.Opens) ≤ U from h)).op).hom

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

def resLE (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U) (x : I.ideal U) :
    I.ideal V :=
  ⟨sres h (x : Γ(X, U)), I.ideal_le_comap_ideal h x.2⟩

@[simp] lemma coe_resLE (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U)
    (x : I.ideal U) : (I.resLE h x : Γ(X, V)) = sres h (x : Γ(X, U)) := rfl

structure IdealHom (I J : X.IdealSheafData) : Type u where

  app : ∀ U : X.affineOpens, I.ideal U →ₗ[Γ(X, U)] J.ideal U

  coe_app_resLE : ∀ {U V : X.affineOpens} (h : V ≤ U) (x : I.ideal U),
    ((app V (I.resLE h x) : J.ideal V) : Γ(X, V)) = sres h ((app U x : J.ideal U) : Γ(X, U))

namespace IdealHom

variable {I J K : X.IdealSheafData}

@[ext]
lemma ext {φ ψ : IdealHom I J} (h : φ.app = ψ.app) : φ = ψ := by
  cases φ; cases ψ; congr

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

instance : AddCommGroup (IdealHom I J) :=
  Function.Injective.addCommGroup (fun φ : IdealHom I J => φ.app)
    (fun _ _ h => ext h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : SMul Γ(X, ⊤) (IdealHom I J) :=
  ⟨fun s φ => ⟨fun U => sresTop U s • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, SetLike.val_smul, smul_eq_mul, map_mul,
      φ.coe_app_resLE h x, sres_sresTop]⟩⟩

@[simp] lemma smul_app (s : Γ(X, ⊤)) (φ : IdealHom I J) (U : X.affineOpens) :
    (s • φ).app U = sresTop U s • φ.app U := rfl

instance : Module Γ(X, ⊤) (IdealHom I J) where
  one_smul φ := by ext U x; simp
  mul_smul r s φ := by ext U x; simp [mul_smul]
  smul_zero r := by ext U x; simp
  smul_add r φ ψ := by ext U x; simp
  add_smul r s φ := by ext U x; simp [add_smul]
  zero_smul φ := by ext U x; simp

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
    have hle : X.affineBasicOpen f ≤ U := X.affineBasicOpen_le f
    have hres : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = sres hle := rfl
    rw [hres]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      rintro _ ⟨x, rfl⟩
      exact ⟨I.resLE hle x, (φ.coe_app_resLE hle x)⟩
    · rintro _ ⟨y, rfl⟩

      let M : Submodule (Γ(X, X.affineBasicOpen f)) (I.ideal (X.affineBasicOpen f)) :=
        Submodule.comap ((J.ideal _).subtype ∘ₗ φ.app _)
          (Ideal.map (sres hle) (LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U)))
      suffices h : y ∈ M by rw [Submodule.mem_comap] at h; exact h
      have hle' : (I.ideal U).map (sres hle) ≤ M.map (I.ideal _).subtype := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        refine ⟨I.resLE hle ⟨x, hx⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply,
          φ.coe_app_resLE]
        exact Ideal.mem_map_of_mem (sres hle)
          (LinearMap.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩ : ((φ.app U ⟨x, hx⟩ : J.ideal U) : Γ(X, U)) ∈
            LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U))
      have hy : (y : Γ(X, X.affineBasicOpen f)) ∈ (I.ideal U).map (sres hle) :=
        (I.map_ideal_basicOpen U f).ge y.2
      obtain ⟨y', hy', hyy'⟩ := hle' hy
      have : y' = y := Subtype.ext hyy'
      exact this ▸ hy'

@[simp] lemma ideal_range (φ : IdealHom I J) (U : X.affineOpens) :
    φ.range.ideal U = LinearMap.range ((J.ideal U).subtype ∘ₗ φ.app U) := rfl

lemma range_le (φ : IdealHom I J) : φ.range ≤ J := fun U => by
  rintro _ ⟨x, rfl⟩; exact (φ.app U x).2

end IdealHom

end IdealSheafData

end AlgebraicGeometry.Scheme
