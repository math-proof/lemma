import Mathlib

set_option autoImplicit false

universe w v u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

abbrev presheafULift : MorphismProperty (Cᵒᵖ ⥤ Type (max w v)) := P.relative uliftYoneda.{w}

variable {P}

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

namespace Scheme

variable (F : Sheaf Scheme.zariskiTopology.{u} (Type (max w u)))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : (i : ι) → uliftYoneda.{w}.obj (X i) ⟶ F.obj) (hf : ∀ i, MorphismProperty.presheafULift.{w} @IsOpenImmersion (f i))

namespace LocalRepresentabilityULift

variable {F f} (i j k : ι)

end LocalRepresentabilityULift

end Scheme

end AlgebraicGeometry
