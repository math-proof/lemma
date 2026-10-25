-- Carved from Lemma/Definitions/Def_IharaMennickeCarrier.lean: instance decls only.
import Lemma.Gamma0Away.Main
import Lemma.IharaAmalgamMap.Main
import Lemma.Gamma0AwayUnitsChar.Main
import Mathlib.GroupTheory.Subgroup.Simple
import Lemma.IharaMennickeCarrier.Main

open Matrix

open scoped MatrixGroups

namespace Ihara


section Carrier

variable (N q : ℕ)

instance (hNq : Nat.Coprime N q) : (principalCongruenceAway N q hNq).Normal :=
  MonoidHom.normal_ker (slAwayReduction N q hNq)

end Carrier


open scoped MatrixGroups commutatorElement


end Ihara
