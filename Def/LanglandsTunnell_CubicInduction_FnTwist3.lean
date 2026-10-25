import Lemma.LanglandsTunnell.CubicInduction_Carrier

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section DetCharacter

variable (n : ℕ) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def chiDetGL (η : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL n R K → ℂ :=
  fun g => ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

end DetCharacter


section Twist

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def fnTwist3 (η : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL 3 R K → ℂ) : AdelicGL 3 R K → ℂ :=
  fun g => chiDetGL 3 R K η g * φ g


def twistedCentralChar3 (ω η : (AdeleRing R K)ˣ →* ℂˣ) : (AdeleRing R K)ˣ →* ℂˣ :=
  ω * η ^ 3

end Twist

end LanglandsTunnell.CubicInduction

end
