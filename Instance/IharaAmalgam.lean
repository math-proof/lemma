-- Carved from Lemma/Definitions/Def_IharaAmalgam.lean: instance decls only.
import Mathlib.GroupTheory.PushoutI
import Theorem.Matrix.IharaAmalgam
import Def.Matrix_IharaAmalgam

namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups

instance (N q : ℕ) : Group (iharaAmalgam N q) :=
  inferInstanceAs (Group (Monoid.PushoutI (iharaEdge N q)))


end Ihara
