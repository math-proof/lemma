module
public import Mathlib.GroupTheory.Subgroup.Simple
public import Theorem.Matrix.IharaMennickeCarrier
public import Def.Matrix_IharaMennickeCarrier
open Matrix
open scoped MatrixGroups


public section

-- Carved from Lemma/Definitions/Def_IharaMennickeCarrier.lean: instance decls only.

namespace Ihara


section Carrier

variable (N q : ℕ)

instance (hNq : Nat.Coprime N q) : (principalCongruenceAway N q hNq).Normal :=
  MonoidHom.normal_ker (slAwayReduction N q hNq)

end Carrier


open scoped MatrixGroups commutatorElement


end Ihara
