import Mathlib

set_option autoImplicit false

open CategoryTheory Category Opposite

namespace CategoryTheory.Functor

universe w v u

variable {C : Type u} [Category.{v} C] {S : C} (G : (Over S)ᵒᵖ ⥤ Type w)

abbrev OverTotal (T : C) : Type (max w v) := Σ t : T ⟶ S, G.obj (op (Over.mk t))

variable {G}

namespace RepresentableBy


end RepresentableBy

end CategoryTheory.Functor
