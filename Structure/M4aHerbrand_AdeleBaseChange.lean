import Structure.M4aHerbrand_IdeleClassVocab

set_option autoImplicit false

open NumberField TensorProduct

namespace M4aHerbrand

noncomputable section

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]


structure AdeleBaseChange where
  β : AdeleRing R E →+* AdeleRing S F
  β_compat : ∀ e : E, β (algebraMap E (AdeleRing R E) e) =
    algebraMap F (AdeleRing S F) (algebraMap E F e)
  tensorEquiv : letI := β.toAlgebra
    ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F
  tensorEquiv_one_tmul : ∀ f : F,
    letI := β.toAlgebra
    tensorEquiv ((1 : AdeleRing R E) ⊗ₜ[E] f) = algebraMap F (AdeleRing S F) f

namespace AdeleBaseChange

variable {R E S F}


end AdeleBaseChange

section SelfInhabitant

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]


end SelfInhabitant

end

end M4aHerbrand
