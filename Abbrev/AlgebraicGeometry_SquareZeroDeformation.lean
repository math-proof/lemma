import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Instance.AlgebraicGeometry_SquareZeroDeformation

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TrivSqZeroExt NeronModelInfra

namespace AlgebraicGeometry

namespace SquareZero

variable (K : Type u) [Field K]
variable (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

abbrev spec : Scheme.{u} := Spec (CommRingCat.of (TrivSqZeroExt K V))

end SquareZero

section TangentPoints

variable {K : Type u} [Field K] {X : Scheme.{u}}


namespace RelPicard

variable {K : Type u} [Field K] {C : Scheme.{u}}


end RelPicard

end AlgebraicGeometry

end
