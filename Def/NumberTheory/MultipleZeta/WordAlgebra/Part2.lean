/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean -/

import Mathlib.Algebra.FreeAlgebra
import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index
import Theorem.NumberTheory.MultipleZeta.WordAlgebra


namespace MetaMathlibExt.MultipleZeta

/-- Empty-or-admissible predicate for indices used in the algebraic `H^0` API.
This avoids importing the later analytic series layer solely for its analogous
depth-based predicate. -/
def IsHZeroIndex (idx : Index) : Prop :=
  idx.IsAdmissible ∨ idx.entries = []

/-- Indices whose Hoffman words belong to the `H^0` word subalgebra. -/
def HZeroIndex : Type := { idx : Index // IsHZeroIndex idx }

end MetaMathlibExt.MultipleZeta
