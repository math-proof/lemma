set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_Dieudonne_WittGroupHopf.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace Dieudonne_WittGroupHopf

scoped notation "𝒪" => Coord R p n J

scoped notation "T" => Coord R p n J ⊗[R] (Coord R p n J ⊗[R] Coord R p n J)

end Dieudonne_WittGroupHopf
