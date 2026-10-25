-- Carved from Lemma/Definitions/Def_ModularCurve_KatzLevelPTorusPairs.lean: instance decls only.
import Mathlib
import Instance.ModularCurve_KatzLevelP
import Instance.ModularCurve_KatzLevelPUniversal
import Instance.ModularCurve_KatzLevelPClassifyingMaps
import Lemma.ModularCurve.KatzLevelPTorusPairs

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section Torus

variable (p : ℕ) (a b : ℕ)

instance : CommRing (TorusRing p a b) := inferInstanceAs (CommRing (Localization.Away (torusDenom p a b)))

instance : Algebra (TorusQRing p a b) (TorusRing p a b) :=
  inferInstanceAs (Algebra (TorusQRing p a b) (Localization.Away (torusDenom p a b)))

instance : IsLocalization.Away (torusDenom p a b) (TorusRing p a b) :=
  inferInstanceAs (IsLocalization.Away (torusDenom p a b) (Localization.Away (torusDenom p a b)))

instance : Algebra (UnivBasisRing p) (TorusRing p a b) :=
  inferInstanceAs (Algebra (UnivBasisRing p) (Localization.Away (torusDenom p a b)))

instance : IsScalarTower (UnivBasisRing p) (TorusQRing p a b) (TorusRing p a b) :=
  inferInstanceAs (IsScalarTower (UnivBasisRing p) (TorusQRing p a b) (Localization.Away (torusDenom p a b)))

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (D' : LevelPData T)

end Torus

end LevelP

end ModularCurve

end
