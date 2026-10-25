set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_GaloisRep_InertiaRing.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace GaloisRep_InertiaRing

scoped notation "ℚ̄" => AlgebraicClosure ℚ

scoped notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

end GaloisRep_InertiaRing
