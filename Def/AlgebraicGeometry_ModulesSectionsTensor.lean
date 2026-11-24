module
public import Mathlib
public import Theorem.LinearMap.InternalHom
public import Instance.SheafOfModules_Monoidal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


public section

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Hom

variable (L M : X.Modules)

def tensorSectionsHom : L.val ⊗ M.val ⟶
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj (L ⊗ M) :=
  (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val) ≫
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).map (tensorIsoSheafify L M).hom

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

def tensorSections (s : Γ(L, U)) (t : Γ(M, U)) : Γ(L ⊗ M, U) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M, U))
    ((tensorSectionsHom L M).app (op U)).hom
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))

variable (L M U) in

def tensorSectionsBilin : Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U) :=
  LinearMap.mk₂ Γ(X, U) tensorSections tensorSections_add_left tensorSections_smul_left
    tensorSections_add_right tensorSections_smul_right

end Sections

section Pow

variable {L : X.Modules} {U : X.Opens}

variable (U) in

def unitSection : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))

def tensorPowSection (s : Γ(L, U)) : (n : ℕ) → Γ(L.tensorPow n, U)
  | 0 => unitSection U
  | n + 1 => tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection s n) s

end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

def IsFrameOn (s : Γ(M, U)) (V : X.Opens) : Prop :=
  ∀ ⦃W : X.Opens⦄ (hWU : W ≤ U), W ≤ V →
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W))


end Frame

end AlgebraicGeometry.Scheme.Modules

end
