set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_AlgebraicGeometry_ProjSpace.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace AlgebraicGeometry_ProjSpace

scoped notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

scoped notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

scoped notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

end AlgebraicGeometry_ProjSpace
