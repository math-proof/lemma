/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part6


section

namespace MetaMathlibExt

open scoped BigOperators

instance subsingleton_cell_zero_aux : Subsingleton (latticeCell 0) := by
  constructor
  intro x y
  funext k
  exact Fin.elim0 k

instance latticeCellDecEq_aux (d : ℕ) : DecidableEq (latticeCell d) :=
  inferInstanceAs (DecidableEq (Fin d → ℤ))

end MetaMathlibExt
end
