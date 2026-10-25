set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_ModularCurve_FullLevelJacobian.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace ModularCurve_FullLevelJacobian

scoped notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

end ModularCurve_FullLevelJacobian
