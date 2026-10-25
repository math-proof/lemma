import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

namespace DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} (x' : X' ⟶ S')

noncomputable def unitMap : X' ⟶ pullback (x' ≫ s) s :=
  pullback.lift (𝟙 X') x' (by rw [Category.id_comp])

noncomputable def proj₁₃ :
    pullback (pullback.snd (x' ≫ s) s ≫ s) s ⟶ pullback (x' ≫ s) s :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition]; exact pullback.condition)


variable {s x'} in

noncomputable def actMap (act : pullback (x' ≫ s) s ⟶ X') (h : act ≫ x' = pullback.snd _ _) :
    pullback (pullback.snd (x' ≫ s) s ≫ s) s ⟶ pullback (x' ≫ s) s :=
  pullback.lift (pullback.fst _ _ ≫ act) (pullback.snd _ _)
    (by rw [Category.assoc, reassoc_of% h]; exact pullback.condition)

variable {s x'} in
variable {s x'} in


end DescentAction

structure DescentAction {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} (x' : X' ⟶ S') where

  act : pullback (x' ≫ s) s ⟶ X'
  act_comp : act ≫ x' = pullback.snd _ _
  unit_act : DescentAction.unitMap s x' ≫ act = 𝟙 X'
  trans : DescentAction.actMap act act_comp ≫ act = DescentAction.proj₁₃ s x' ≫ act

namespace DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S)


variable {s} in


end DescentAction

namespace DescentAction

variable {S S' : Scheme.{u}} {s : S' ⟶ S} {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction s x')


end DescentAction

namespace DescentAction

section repAct

variable {S S' : Scheme.{u}} (s : S' ⟶ S) (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) {X' : Scheme.{u}} (x' : X' ⟶ S')
  (hX' : ((Over.map s).op ⋙ G).RepresentableBy (Over.mk x'))


end repAct

end DescentAction

namespace DescentAction

section rep

variable {S S' : Scheme.{u}} (s : S' ⟶ S) (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) {X' : Scheme.{u}} (x' : X' ⟶ S')
  (hX' : ((Over.map s).op ⋙ G).RepresentableBy (Over.mk x'))
  {X : Scheme.{u}} (f : X ⟶ S) (e : pullback f s ≅ X') (he : e.hom ≫ x' = pullback.snd f s)


section withζ

variable (ζ : G.obj (op (Over.mk f))) (hζ : G.map (cover s f).op ζ = univBC s G x' hX' f e he)

include hζ in


end withζ


end rep

end DescentAction

end AlgebraicGeometry
