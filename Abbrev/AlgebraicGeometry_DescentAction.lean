import Mathlib
import Structure.AlgebraicGeometry_DescentAction

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

namespace DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} (x' : X' ⟶ S')


end DescentAction


namespace DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S)

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

noncomputable abbrev leftHom {T : Over S} (n : (Over.pullback s).obj T ⟶ Over.mk x') : pullback T.hom s ⟶ X' := n.left

section withζ


end withζ

end rep

end DescentAction

end AlgebraicGeometry
