import Mathlib

set_option autoImplicit false

universe w v u

open CategoryTheory

namespace CategoryTheory
namespace Subfunctor

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

def ofIsTerminal {X : C} (hX : Limits.IsTerminal X) (s : Set (F.obj X)) :
    Subfunctor F where
  obj U := F.map (hX.from U) ⁻¹' s
  map {U V} i := by
    simp only [← Set.preimage_comp, ← hX.comp_from i, F.map_comp]
    rfl

end Subfunctor
end CategoryTheory
