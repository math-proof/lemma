module
public import Mathlib.GroupTheory.PushoutI
public import Theorem.Matrix.IharaAmalgam
public import Def.Matrix_IharaAmalgam


public section

-- Carved from Lemma/Definitions/Def_IharaAmalgam.lean: instance decls only.

namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups

instance (N q : ℕ) : Group (iharaAmalgam N q) :=
  inferInstanceAs (Group (Monoid.PushoutI (iharaEdge N q)))


end Ihara
