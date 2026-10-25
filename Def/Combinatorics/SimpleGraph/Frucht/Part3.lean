/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Combinatorics.SimpleGraph.Frucht.Part2


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

noncomputable def fruchtShiftIso (N : ℕ) {G : Type*} [Group G] [DecidableEq G]
    [Fintype G] (e : G ≃ Fin N) (a : G) :
    fruchtGraph N e ≃g fruchtGraph N e :=
  RelIso.mk (fruchtShift N a) (fun {v w} => (fruchtShift_adj N e a v w).symm)

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
