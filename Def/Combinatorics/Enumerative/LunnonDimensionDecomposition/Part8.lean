/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Instance.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part3


section

namespace MetaMathlibExt

open scoped BigOperators

-- compress/expand on Finsets (images)
noncomputable def compressSet_aux2 (d : ℕ) (A : Finset (Fin d))
    (S : Finset (latticeCell d)) : Finset (latticeCell A.card) :=
  Finset.image (compressCell_aux2 d A) S

noncomputable def expandSet_aux2 (d : ℕ) (A : Finset (Fin d))
    (T : Finset (latticeCell A.card)) : Finset (latticeCell d) :=
  Finset.image (expandCell_aux2 d A) T

end MetaMathlibExt
end
