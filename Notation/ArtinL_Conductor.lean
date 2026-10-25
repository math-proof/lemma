set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_ArtinL_Conductor.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace ArtinL_Conductor

scoped notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

scoped notation "ℚbar" => AlgebraicClosure ℚ

end ArtinL_Conductor
