import Instance.NumberField_AdelicHaar

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct
open scoped Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

open scoped Classical in

def idealBound (N : Ideal R) (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ) :=
  if N = ⊥ then 0
  else WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ))

section IdealBound

variable {R}


end IdealBound

section Local

variable {R K} (v : HeightOneSpectrum R)


end Local

section Projections


end Projections

section FiniteAdelic

def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, x v ∈ v.adicCompletionIntegers K}

def idealBall (N : Ideal R) : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, Valued.v (x v) ≤ idealBound R N v}

variable {R K}

section Coe
variable (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R)
end Coe


variable (R K)


variable [Module.Free ℤ R] [Module.Finite ℤ R]


end FiniteAdelic

section FiniteLevel

structure IsLevelZeroMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop where
  integral : ∀ i j, m i j ∈ integralFiniteAdeles R K
  lowerLeft : m 1 0 ∈ idealBall R K N

structure IsLevelOneMatrix (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Prop extends IsLevelZeroMatrix R K N m where
  lowerRight : m 1 1 - 1 ∈ idealBall R K N

variable {R K}
variable {N : Ideal R}


namespace IsLevelZeroMatrix


variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}


end IsLevelZeroMatrix

namespace IsLevelOneMatrix


variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}


end IsLevelOneMatrix

variable (R K) (N)


variable {R K N}


variable (R K N)


variable {R K} in


variable {N} in

variable {N} in

variable {N} in


variable {N} in


section Compact

variable [Module.Free ℤ R] [Module.Finite ℤ R]


end Compact

end FiniteLevel

section Adelic

variable (N : Ideal R)


variable {R K N}


variable (R K N)


variable {N} in


variable {N} in


end Adelic

section Gen


variable (v : HeightOneSpectrum R)

open scoped Classical in


open scoped Classical in

open scoped Classical in


variable {R K v}


variable (K v)


variable (R)


variable {R K v}


end Gen

end NumberField.AdelicLevel

end
