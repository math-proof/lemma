-- Carved from Lemma/Definitions/Def_ModularCurve_KatzLevelPUniversal.lean: instance decls only.
import Mathlib
import Instance.ModularCurve_KatzLevelP
import Lemma.ModularCurve.KatzLevelPUniversal

set_option autoImplicit false

universe u

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section TorsionPoint

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ)

instance : CommRing (PsiRoot W p) := inferInstanceAs (CommRing (AdjoinRoot (W.preΨ p)))

instance : Algebra B (PsiRoot W p) := inferInstanceAs (Algebra B (AdjoinRoot (W.preΨ p)))

instance : CommRing (TorsionPointRing W p) :=
  inferInstanceAs (CommRing (AdjoinRoot (torsionQuadratic W p)))

instance : Algebra (PsiRoot W p) (TorsionPointRing W p) :=
  inferInstanceAs (Algebra (PsiRoot W p) (AdjoinRoot (torsionQuadratic W p)))

instance : Algebra B (TorsionPointRing W p) :=
  inferInstanceAs (Algebra B (AdjoinRoot (torsionQuadratic W p)))

instance : IsScalarTower B (PsiRoot W p) (TorsionPointRing W p) :=
  inferInstanceAs (IsScalarTower B (PsiRoot W p) (AdjoinRoot (torsionQuadratic W p)))

end TorsionPoint

section TwoPoints

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ)

instance : Algebra B (TwoPointRing W p) := (TwoPointRing.ofBase W p).toAlgebra

instance : IsScalarTower B (TorsionPointRing W p) (TwoPointRing W p) :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [TwoPointRing.algebraMap_onePoint_eq W p, TorsionPointRing.algebraMap_eq W p]; rfl)

instance : CommRing (BasisRing W p) := inferInstanceAs (CommRing (Localization.Away (indepDenom W p)))

instance : Algebra (TwoPointRing W p) (BasisRing W p) :=
  inferInstanceAs (Algebra (TwoPointRing W p) (Localization.Away (indepDenom W p)))

instance : IsLocalization.Away (indepDenom W p) (BasisRing W p) :=
  inferInstanceAs (IsLocalization.Away (indepDenom W p) (Localization.Away (indepDenom W p)))

instance : Algebra B (BasisRing W p) := (BasisRing.ofBase W p).toAlgebra

instance : IsScalarTower B (TwoPointRing W p) (BasisRing W p) :=
  IsScalarTower.of_algebraMap_eq' rfl

end TwoPoints

variable (p : ℕ)

instance : CommRing (UnivBase p) := inferInstanceAs (CommRing (Localization.Away (pDelta p)))

instance : Algebra (MvPolynomial (Fin 5) ℤ) (UnivBase p) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin 5) ℤ) (Localization.Away (pDelta p)))

instance : IsLocalization.Away (pDelta p) (UnivBase p) :=
  inferInstanceAs (IsLocalization.Away (pDelta p) (Localization.Away (pDelta p)))

end LevelP


end ModularCurve

end
