set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_AlgebraicGeometry_ProjTwistDatum.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace AlgebraicGeometry_ProjTwistDatum

scoped notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

scoped notation "S" => MvPolynomial (Fin (N + 1)) A

end AlgebraicGeometry_ProjTwistDatum
