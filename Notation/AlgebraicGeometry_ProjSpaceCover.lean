set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_AlgebraicGeometry_ProjSpaceCover.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace AlgebraicGeometry_ProjSpaceCover

scoped notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

end AlgebraicGeometry_ProjSpaceCover
