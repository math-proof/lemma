import Structure.NumberField_AdelicLevel
import Def.LocalNewvector_CongruenceSubgroupK1
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AdelicDock

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]


variable (v : HeightOneSpectrum R)

open scoped Classical in


open scoped Classical in

open scoped Classical in


structure IsLocalLevelOne (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Prop where
  integral : ∀ i j, m i j ∈ v.adicCompletionIntegers K
  lowerLeft : Valued.v (m 1 0) ≤ AdelicLevel.idealBound R N v
  lowerRight : Valued.v (m 1 1 - 1) ≤ AdelicLevel.idealBound R N v


end Generic

section Rat

variable (p : ℕ) [Fact p.Prime]


end Rat

end AdelicDock

end
