/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SchurZassenhaus.lean -/

import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Order.CompletePartialOrder

section
/-!
# Schur–Zassenhaus theorem

Records conjugacy of complements for the Schur–Zassenhaus theorem: any two complements of
a normal Hall subgroup in a finite group are conjugate under the standard solvability
hypothesis. Hall is `Nat.Coprime (Nat.card N) N.index`. Complement existence is already
in `Mathlib.GroupTheory.SchurZassenhaus`.
-/

namespace MathlibExt.GroupTheory.SchurZassenhausWanted

open scoped Pointwise
open MulAction MulOpposite Subgroup QuotientGroup Function

private def clsC {G : Type*} [Group G] (H : Subgroup G) [IsMulCommutative H] [H.FiniteIndex]
    (K : Subgroup G) (hK : H.IsComplement' K) : H.QuotientDiff :=
  Quotient.mk'' ⟨(K : Set G), hK.symm⟩
end MathlibExt.GroupTheory.SchurZassenhausWanted
end
