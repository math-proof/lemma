-- Carved from Lemma/Definitions/Def_LanglandsTunnell_LiftTraceSeed.lean: instance decls only.
import Def.AutomorphicForm_HeckeEigensystem
import Def.LanglandsTunnell_ExplicitLift
import Def.LanglandsTunnell_LiftTraceSeed

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain FLT.ExplicitLift


section PrimeOver

variable {L : Type*} [Field L] [NumberField L] (H : Subgroup (L ≃ₐ[ℚ] L))

variable (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)))

instance primeOver_isMaximal : (primeOver H w).IsMaximal := (exists_prime_over H w).choose_spec.1

instance primeOver_finite : Finite (𝓞 L ⧸ primeOver H w) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (primeOver_ne_bot H w)

end PrimeOver


end LanglandsTunnell.P2

end
