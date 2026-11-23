-- Carved from Lemma/Definitions/Def_IharaMennickeCarrier.lean: instance decls only.
import Mathlib.GroupTheory.Subgroup.Simple
import Theorem.Matrix.IharaMennickeCarrier
import Def.Matrix_IharaMennickeCarrier

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
