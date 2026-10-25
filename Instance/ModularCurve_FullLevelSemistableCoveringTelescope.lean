-- Carved from Lemma/Definitions/Def_ModularCurve_FullLevelSemistableCoveringTelescope.lean: instance decls only.
import Lemma.ModularCurve.FullLevelSemistableCovering
import Lemma.ModularCurve.FullLevelSemistableCoveringTelescope

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel.SemistableCovering

open AlgebraicCurve IsLocalRing


variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
variable (𝒞 : SemistableCovering q M' A W)

instance instFieldSumFbar : ∀ j, Field (𝒞.sumFbar j)
  | .inl ℓ => 𝒞.instFieldIg ℓ
  | .inr s => 𝒞.instFieldSS s

instance instAlgebraSumFbar : ∀ j, Algebra (ResidueField A) (𝒞.sumFbar j)
  | .inl ℓ => 𝒞.instAlgebraIg ℓ
  | .inr s => 𝒞.instAlgebraSS s

instance instHasPrincipalDivisorsSumFbar : ∀ j, HasPrincipalDivisors (ResidueField A) (𝒞.sumFbar j)
  | .inl ℓ => 𝒞.hasPrincipalDivisors_Ig ℓ
  | .inr s => 𝒞.hasPrincipalDivisors_SS s

instance instFieldTeleFbar (i : Fin 𝒞.teleN) : Field (𝒞.teleFbar i) := 𝒞.instFieldSumFbar _
instance instAlgebraTeleFbar (i : Fin 𝒞.teleN) : Algebra (ResidueField A) (𝒞.teleFbar i) := 𝒞.instAlgebraSumFbar _
instance instHasPrincipalDivisorsTeleFbar (i : Fin 𝒞.teleN) :
    HasPrincipalDivisors (ResidueField A) (𝒞.teleFbar i) := 𝒞.instHasPrincipalDivisorsSumFbar _

end ModularCurve.FullLevel.SemistableCovering

end
