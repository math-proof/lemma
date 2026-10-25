import Lemma.LanglandsTunnell.CubicInduction_Carrier

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Congruence

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

def congruenceK1 (c : ℕ) : Set (GL (Fin 3) (v.adicCompletion K)) :=
  {k | k ∈ localMaximalCompact3 R K v ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ))}

end Congruence

end LanglandsTunnell.CubicInduction

end
