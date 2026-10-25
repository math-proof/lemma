set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_AutomorphicForm_WeylSelectors.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace AutomorphicForm_WeylSelectors

scoped notation "𝔸" => AdeleRing (𝓞 F) F

scoped notation "𝔸∞" => InfiniteAdeleRing F

scoped notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

end AutomorphicForm_WeylSelectors
