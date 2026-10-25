-- Carved from Lemma/Definitions/Def_ModularCurve_LevelModuliPackage.lean: instance decls only.
import Mathlib
import Lemma.ModularCurve.LevelModuliPackage

set_option autoImplicit false

universe u

namespace ModularCurve

namespace LevelModuliDatum

variable {A : Type u} [CommRing A]

instance Twist.instCommRing (σA : A ≃+* A) (T : Type u) [CommRing T] : CommRing (Twist σA T) :=
  inferInstanceAs (CommRing T)

instance Twist.instAlgebra (σA : A ≃+* A) (T : Type u) [CommRing T] [Algebra A T] : Algebra A (Twist σA T) :=
  ((algebraMap A T).comp σA.toRingHom).toAlgebra

end LevelModuliDatum


end ModularCurve
