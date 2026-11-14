-- Carved from Lemma/Definitions/Def_IharaAmalgam.lean: instance decls only.
import Lemma.Matrix.IharaIota
import Mathlib.GroupTheory.PushoutI
import Lemma.Matrix.IharaAmalgam

namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups

instance (N q : ℕ) : Group (iharaAmalgam N q) :=
  inferInstanceAs (Group (Monoid.PushoutI (iharaEdge N q)))


end Ihara
