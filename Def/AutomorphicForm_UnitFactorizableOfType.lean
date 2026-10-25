import Lemma.AutomorphicForm.LocalOrbitalBase
import Lemma.AutomorphicForm.IsotypicCuspSpace

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace AutomorphicForm

section TierRefined

variable (K : Type) [Field K] [NumberField K]

def IsUnitFactorizableOfTypeAt (tys : ArchTypeFamily K)
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsUnitFactorizableAt K U S f ∧ IsArchBiFinite K tys f

end TierRefined

end AutomorphicForm
