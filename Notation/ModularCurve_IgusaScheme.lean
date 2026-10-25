set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_ModularCurve_IgusaScheme.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace ModularCurve_IgusaScheme

scoped notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)

scoped notation "F" => ↥(modularFunctionFieldFull N)

end ModularCurve_IgusaScheme
