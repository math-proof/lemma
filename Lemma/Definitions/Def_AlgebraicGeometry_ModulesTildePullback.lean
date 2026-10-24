import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in

def Scheme.Modules.pushforwardSpecCompΓIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents
    (fun N => LinearEquiv.toModuleIso
      (X₁ := (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj N)
      (X₂ := (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj N)
      { __ := AddEquiv.refl _
        map_smul' := fun r m => by
          change (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom).obj _ at m
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          simp only [AddEquiv.toFun_eq_coe, AddEquiv.refl_apply, RingHom.id_apply]
          have h1 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of R)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          have h2 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of S)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          simp only [h1, h2, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]
          congr 1
          have key := congrArg (fun ψ : R ⟶ Γ(Spec S, ⊤) => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality φ)
          simp only [Scheme.ΓSpecIso_inv, StructureSheaf.globalSectionsIso_hom] at key
          exact key.symm })
    (fun f => by ext; rfl)

def tilde.functorCompPullbackSpecIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  Adjunction.leftAdjointUniq
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (Scheme.Modules.pushforwardSpecCompΓIso φ).symm)

def tilde.pullbackSpecIso (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (tilde.functorCompPullbackSpecIso φ).app M

@[simp] theorem tilde.functorCompPullbackSpecIso_app (M : ModuleCat.{u} R) :
    (tilde.functorCompPullbackSpecIso φ).app M = tilde.pullbackSpecIso φ M := rfl

theorem tilde.pullbackSpecIso_hom_naturality {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Scheme.Modules.pullback (Spec.map φ)).map ((tilde.functor R).map f) ≫
        (tilde.pullbackSpecIso φ M').hom =
      (tilde.pullbackSpecIso φ M).hom ≫ (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map f) :=
  (tilde.functorCompPullbackSpecIso φ).hom.naturality f

end AlgebraicGeometry

end
