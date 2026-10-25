import Mathlib
import Def.AutomorphicForm_HeckeEigensystem
import Theorems.Thm_AutomorphicForm_satakePow_add_pow

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

noncomputable section

namespace AutomorphicForm


variable {R : Type*} [CommRing R]

def heckeLFactorPoly (s e : R) : Polynomial R :=
  1 - C s * X + C e * X ^ 2


def HeckeEigensystem.localLFactor {F : Type*} [Field F] [NumberField F]
    (π : HeckeEigensystem F R) (v : HeightOneSpectrum (𝓞 F)) : Polynomial R :=
  heckeLFactorPoly (π.a v) (π.b v)


section ConductorCarrier

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]

def HasBaseChangeLevelLaw (𝔡 : Ideal (𝓞 L)) (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) : Prop :=
  Φ.level ∣ 𝔡 * Ideal.map (algebraMap (𝓞 E) (𝓞 L)) π.level

end ConductorCarrier

end AutomorphicForm

end
