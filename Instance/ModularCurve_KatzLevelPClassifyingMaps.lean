-- Carved from Lemma/Definitions/Def_ModularCurve_KatzLevelPClassifyingMaps.lean: instance decls only.
import Mathlib
import Instance.ModularCurve_KatzLevelP
import Instance.ModularCurve_KatzLevelPUniversal
import Lemma.ModularCurve.KatzLevelPClassifyingMaps

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP


section VC

variable (p : ℕ)

instance : CommRing (VCRing p) := inferInstanceAs (CommRing (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

instance : Algebra (VCPoly p) (VCRing p) :=
  inferInstanceAs (Algebra (VCPoly p) (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

instance : IsLocalization.Away (MvPolynomial.X 0 : VCPoly p) (VCRing p) :=
  inferInstanceAs (IsLocalization.Away (MvPolynomial.X 0 : VCPoly p) (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

instance : Algebra (UnivBasisRing p) (VCRing p) :=
  inferInstanceAs (Algebra (UnivBasisRing p) (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

instance : IsScalarTower (UnivBasisRing p) (VCPoly p) (VCRing p) :=
  inferInstanceAs (IsScalarTower (UnivBasisRing p) (VCPoly p) (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (C : VariableChange T)

end VC

section Borel

variable (p : ℕ) (a : ℕ)

instance : Algebra (UnivBasisRing p) (BorelPRing p a) := (BorelPRing.ofUniv p a).toAlgebra

instance : IsScalarTower (UnivBasisRing p) (BorelQRing p a) (BorelPRing p a) :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [BorelPRing.algebraMap_eq, BorelPRing.ofUniv, TorsionPointRing.algebraMap_eq,
      AdjoinRoot.algebraMap_eq])

instance : CommRing (BorelRing p a) := inferInstanceAs (CommRing (Localization.Away (borelDenom p a)))

instance : Algebra (BorelPRing p a) (BorelRing p a) :=
  inferInstanceAs (Algebra (BorelPRing p a) (Localization.Away (borelDenom p a)))

instance : IsLocalization.Away (borelDenom p a) (BorelRing p a) :=
  inferInstanceAs (IsLocalization.Away (borelDenom p a) (Localization.Away (borelDenom p a)))

instance : Algebra (UnivBasisRing p) (BorelRing p a) :=
  inferInstanceAs (Algebra (UnivBasisRing p) (Localization.Away (borelDenom p a)))

instance : IsScalarTower (UnivBasisRing p) (BorelPRing p a) (BorelRing p a) :=
  inferInstanceAs (IsScalarTower (UnivBasisRing p) (BorelPRing p a) (Localization.Away (borelDenom p a)))

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (D' : LevelPData T)

end Borel

end LevelP

end ModularCurve

end
