-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ModulesGlueOfCocycle.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.ModulesSectionsTensor
import Lemma.AlgebraicGeometry.ModulesGlueOfCocycle

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u}


open GlueOfCocycle


namespace GlueOfCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U) (T : X.Opens)

variable {c T}

variable (c T)

noncomputable instance : SMul Γ(X, T) (families c T) where
  smul g x := ⟨fun i => rO inf_le_left g * x.1 i, by
    have hx := x.2
    rw [mem_families] at hx ⊢
    intro i j
    simp only [map_mul, rO_rO]
    rw [hx i j, rO_irrel ((leTi T i j).trans inf_le_left) ((leTj T i j).trans inf_le_left)]
    ring⟩

noncomputable instance : Module Γ(X, T) (families c T) where
  one_smul x := by apply Subtype.ext; funext i; rw [smul_val]; simp
  mul_smul a b x := by apply Subtype.ext; funext i; simp only [smul_val, map_mul, mul_assoc]
  smul_zero a := by apply Subtype.ext; funext i; rw [smul_val]; simp
  smul_add a x y := by apply Subtype.ext; funext i; simp only [smul_val, AddSubgroup.coe_add, Pi.add_apply, mul_add]
  add_smul a b x := by apply Subtype.ext; funext i; simp only [smul_val, map_add, add_mul, AddSubgroup.coe_add, Pi.add_apply]
  zero_smul x := by apply Subtype.ext; funext i; rw [smul_val]; simp

variable {T}

noncomputable instance instModulePreGlue (T : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj T) ((preGlue c).obj T) :=
  inferInstanceAs (Module Γ(X, T.unop) (families c T.unop))

end GlueOfCocycle

variable {U : ι → X.Opens}

end AlgebraicGeometry.Scheme.Modules
