import Abbrev.AlgebraicGeometry_IdealSheafModule
import Instance.AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}


abbrev zeroScheme (s : 𝟙_ X.Modules ⟶ M) : Scheme.{u} :=
  (zeroSchemeIdeal s).subscheme


end Scheme.Modules

end AlgebraicGeometry

end
