-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_SquareZeroDeformation.lean: instance decls only.
import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TrivSqZeroExt NeronModelInfra

namespace AlgebraicGeometry

namespace SquareZero

variable (K : Type u) [Field K]
variable (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

instance isLocalRing : IsLocalRing (TrivSqZeroExt K V) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : a.fst = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h, sub_zero]
      exact isUnit_one
    · left
      exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (Ne.isUnit h)

instance isLocalRing' : IsLocalRing (CommRingCat.of (TrivSqZeroExt K V)) :=
  SquareZero.isLocalRing K V

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
variable {W' : Type u} [AddCommGroup W'] [Module K W'] [Module Kᵐᵒᵖ W'] [IsCentralScalar K W']

end SquareZero


end
end
