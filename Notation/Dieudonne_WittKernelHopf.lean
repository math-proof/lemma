set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_Dieudonne_WittKernelHopf.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace Dieudonne_WittKernelHopf

scoped notation "𝒪" => WittGroup.Coord k p n J

scoped notation "I" => ideal k p n a b J

scoped notation "πI" => (Ideal.Quotient.mk (ideal k p n a b J))

end Dieudonne_WittKernelHopf
