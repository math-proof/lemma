set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_Deformations_TaylorWilesLocal.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace Deformations_TaylorWilesLocal

scoped notation "M₂ " k => Matrix (Fin 2) (Fin 2) k

end Deformations_TaylorWilesLocal
