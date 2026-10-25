set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_MazurAdmissible_GaloisModule.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace MazurAdmissible_GaloisModule

scoped notation "Qbar" => AlgebraicClosure ℚ

end MazurAdmissible_GaloisModule
