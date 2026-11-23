module

public import Mathlib

public import Def.AlgebraicGeometry_OModulePresheafHom
public import Instance.AlgebraicGeometry_OModulePresheafInternalHom
public import Abbrev.AlgebraicGeometry_OModulePresheafInternalHom

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F G : OModulePresheaf π)


public theorem mem_homSub_iff (U : V.Opens) (φ : HomPi F G U) :
    φ ∈ homSub F G U ↔ (∀ (W : AffBelow U) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), φ W (a • x) = a • φ W x) ∧
      ∀ (W W' : AffBelow U) (h : W.1.1 ≤ W'.1.1) (x : F.obj W'.1.1), φ W (F.res h x) = G.res h (φ W' x) :=
  Iff.rfl


public theorem smul_comm_sections (W : V.Opens) (c : R) (b : Γ(V, W)) (y : G.obj W) : c • (b • y) = b • (c • y) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π W
  rw [← algebraMap_smul (A := Γ(V, W)) c (b • y), ← algebraMap_smul (A := Γ(V, W)) c y, smul_smul, smul_smul,
    mul_comm]


public theorem sectionsSMul_apply (U : V.Opens) (a : Γ(V, U)) (φ : homSub F G U) (W : AffBelow U) (x : F.obj W.1.1) :
    (sectionsSMul F G U a φ).1 W x = (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x := rfl


public theorem sections_smul_apply (U : V.Opens) (a : Γ(V, U)) (φ : homSub F G U) (W : AffBelow U) (x : F.obj W.1.1) :
    (a • φ).1 W x = (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x := rfl


public theorem homRes_apply {U U' : V.Opens} (h : U ≤ U') (φ : homSub F G U') (W : AffBelow U) :
    (homRes F G h φ).1 W = φ.1 ⟨W.1, W.2.trans h⟩ := rfl


public theorem internalHom_obj (U : V.Opens) : (internalHom F G).obj U = homSub F G U := rfl


public theorem internalHom_res_apply {U U' : V.Opens} (h : U ≤ U') (φ : (internalHom F G).obj U') (W : AffBelow U) :
    ((internalHom F G).res h φ).1 W = φ.1 ⟨W.1, W.2.trans h⟩ := rfl


public theorem internalHom_smul_apply (U : V.Opens) (a : Γ(V, U)) (φ : (internalHom F G).obj U) (W : AffBelow U)
    (x : F.obj W.1.1) : (a • φ).1 W x = (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x := rfl

namespace internalHom


public theorem eval_apply {U : V.Opens} (W : V.affineOpens) (hW : W.1 ≤ U) (φ : (internalHom F G).obj U) (x : F.obj W.1) :
    eval F G W hW φ x = φ.1 ⟨W, hW⟩ x := rfl


@[simp] public theorem toAffHom_app (φ : (internalHom F G).obj ⊤) (W : V.affineOpens) (x : F.obj W.1) :
    (toAffHom F G φ).app W x = φ.1 ⟨W, le_top⟩ x := rfl


@[simp] public theorem ofAffHom_apply (ψ : AffHom F G) (W : AffBelow (⊤ : V.Opens)) (x : F.obj W.1.1) :
    (ofAffHom F G ψ).1 W x = ψ.app W.1 x := rfl


public theorem toAffHom_ofAffHom (ψ : AffHom F G) : toAffHom F G (ofAffHom F G ψ) = ψ := rfl


public theorem ofAffHom_toAffHom (φ : (internalHom F G).obj ⊤) : ofAffHom F G (toAffHom F G φ) = φ := rfl

end internalHom

end OModulePresheaf

end AlgebraicGeometry

end
