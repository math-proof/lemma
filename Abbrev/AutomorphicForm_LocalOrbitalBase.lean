import Def.AutomorphicForm_FactorizableTestFn

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

noncomputable section

namespace AutomorphicForm

section IntegralUnits

variable {A : Type*}

end IntegralUnits

section Local

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

end Local

section OrbitalIntegral

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  Subgroup.centralizer {γ}

end OrbitalIntegral

section UnitFactor

variable (K : Type) [Field K] [NumberField K]

end UnitFactor

section Tier

variable (K : Type) [Field K] [NumberField K]

end Tier

section RegularSemisimple

variable {A : Type*} [CommRing A]

end RegularSemisimple

end AutomorphicForm

end
