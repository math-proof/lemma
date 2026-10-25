import Mathlib.NumberTheory.NumberField.AdeleRing

set_option autoImplicit false

open NumberField

namespace M4aHerbrand

noncomputable section

section Carrier

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]


end Carrier

section Descent

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

structure IdeleGaloisDescent where

  act : (F ≃ₐ[E] F) →* RingAut (AdeleRing R F)

  compat : ∀ (g : F ≃ₐ[E] F) (x : F),
    act g (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) (g x)

  continuous_act : ∀ g : F ≃ₐ[E] F, Continuous (act g)

namespace IdeleGaloisDescent

variable {R E F}


end IdeleGaloisDescent

end Descent

section NormDerive

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]


set_option maxSynthPendingDepth 3 in


end NormDerive

section Inhabitant

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]


end Inhabitant

end

end M4aHerbrand
