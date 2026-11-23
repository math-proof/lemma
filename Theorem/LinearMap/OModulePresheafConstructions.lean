module

public import Mathlib

public import Def.AlgebraicGeometry_OModulePresheafHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Instance.AlgebraicGeometry_OModulePresheafConstructions
public import Structure.AlgebraicGeometry_OModulePresheafConstructions
public import Abbrev.AlgebraicGeometry_OModulePresheafConstructions

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover


@[simp] public theorem preimage_U {Z : Scheme.{u}} (i : Z ⟶ V) [IsClosedImmersion i] (K : V.OrderedAffineCover) (j : K.ι) :
    (K.preimage i).U j = i ⁻¹ᵁ K.U j := rfl

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}


@[simp] public theorem prod_obj (F G : OModulePresheaf π) (U : V.Opens) : (F.prod G).obj U = (F.obj U × G.obj U) := rfl

@[simp] public theorem fstHom_app (F G : OModulePresheaf π) (U : V.Opens) (x : (F.prod G).obj U) : (F.fstHom G).app U x = x.1 := rfl

@[simp] public theorem sndHom_app (F G : OModulePresheaf π) (U : V.Opens) (x : (F.prod G).obj U) : (F.sndHom G).app U x = x.2 := rfl


@[simp] public theorem pow_obj (F : OModulePresheaf π) (n : ℕ) (U : V.Opens) : (F.pow n).obj U = (Fin n → F.obj U) := rfl

public theorem pow_res_apply (F : OModulePresheaf π) (n : ℕ) {U U' : V.Opens} (h : U ≤ U') (x : (F.pow n).obj U') (j : Fin n) :
    (F.pow n).res h x j = F.res h (x j) := rfl

variable (π) in


@[simp] public theorem restrOpen_obj (F : OModulePresheaf π) (W₀ U : V.Opens) : (F.restrOpen W₀).obj U = F.obj (U ⊓ W₀) := rfl

public theorem restrOpen_res (F : OModulePresheaf π) (W₀ : V.Opens) {U U' : V.Opens} (h : U ≤ U') :
    (F.restrOpen W₀).res h = F.res (inf_le_inf_right W₀ h) := rfl

section KerImCoker

variable {F G : OModulePresheaf π} (φ : Hom F G)


public theorem range_smul_mem (U : V.Opens) (a : Γ(V, U)) (x : G.obj U) (hx : x ∈ LinearMap.range (φ.app U)) :
    a • x ∈ LinearMap.range (φ.app U) := by
  obtain ⟨s, rfl⟩ := hx; exact ⟨a • s, φ.app_smul U a s⟩


public theorem ker_smul_mem (U : V.Opens) (a : Γ(V, U)) (x : F.obj U) (hx : x ∈ LinearMap.ker (φ.app U)) :
    a • x ∈ LinearMap.ker (φ.app U) :=
  LinearMap.mem_ker.mpr ((φ.app_smul U a x).trans (by rw [LinearMap.mem_ker.mp hx, smul_zero]))


@[simp] public theorem ker_obj (U : V.Opens) : (ker φ).obj U = LinearMap.ker (φ.app U) := rfl

@[simp] public theorem im_obj (U : V.Opens) : (im φ).obj U = LinearMap.range (φ.app U) := rfl

@[simp] public theorem coker_obj (U : V.Opens) : (coker φ).obj U = (G.obj U ⧸ LinearMap.range (φ.app U)) := rfl

public theorem ker_res_coe {U U' : V.Opens} (h : U ≤ U') (x : (ker φ).obj U') : ((ker φ).res h x).1 = F.res h x.1 := rfl

public theorem im_res_coe {U U' : V.Opens} (h : U ≤ U') (x : (im φ).obj U') : ((im φ).res h x).1 = G.res h x.1 := rfl

public theorem coker_res_mk {U U' : V.Opens} (h : U ≤ U') (x : G.obj U') :
    (coker φ).res h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (G.res h x) := rfl

public theorem ker_smul_coe (U : V.Opens) (a : Γ(V, U)) (x : (ker φ).obj U) : (a • x).1 = a • x.1 := rfl

public theorem im_smul_coe (U : V.Opens) (a : Γ(V, U)) (x : (im φ).obj U) : (a • x).1 = a • x.1 := rfl

public theorem coker_smul_mk (U : V.Opens) (a : Γ(V, U)) (x : G.obj U) :
    (a • (show (coker φ).obj U from Submodule.Quotient.mk x)) = (show (coker φ).obj U from Submodule.Quotient.mk (a • x)) := rfl


public theorem kerImSES_inc_app (U : V.Opens) (x : (ker φ).obj U) : (kerImSES φ).inc.app U x = x.1 := rfl

public theorem kerImSES_proj_app (U : V.Opens) (x : F.obj U) : ((kerImSES φ).proj.app U x).1 = φ.app U x := rfl

public theorem imCokerSES_inc_app (U : V.Opens) (x : (im φ).obj U) : (imCokerSES φ).inc.app U x = x.1 := rfl

public theorem imCokerSES_proj_app (U : V.Opens) (x : G.obj U) : (imCokerSES φ).proj.app U x = (show (coker φ).obj U from Submodule.Quotient.mk x) := rfl

end KerImCoker

section Pushforward

variable {Z : Scheme.{u}} (i : Z ⟶ V)


variable (π) in


@[simp] public theorem pushforward_obj (H : OModulePresheaf (i ≫ π)) (U : V.Opens) : (pushforward π i H).obj U = H.obj (i ⁻¹ᵁ U) := rfl

public theorem pushforward_res (H : OModulePresheaf (i ≫ π)) {U U' : V.Opens} (h : U ≤ U') :
    (pushforward π i H).res h = H.res ((Opens.map i.base).monotone h) := rfl

public theorem pushforward_smul (H : OModulePresheaf (i ≫ π)) (U : V.Opens) (a : Γ(V, U)) (x : H.obj (i ⁻¹ᵁ U)) :
    (a • (show (pushforward π i H).obj U from x)) = (show (pushforward π i H).obj U from (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom a • x) := rfl

end Pushforward

section AffHoms

variable (F : OModulePresheaf π)

