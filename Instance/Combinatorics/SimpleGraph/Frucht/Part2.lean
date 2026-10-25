/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Def.Combinatorics.SimpleGraph.Frucht


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

noncomputable instance fruchtGraphDec (N : ℕ) {G : Type*} [Group G] [DecidableEq G]
    [Fintype G] (e : G ≃ Fin N) : DecidableRel (fruchtGraph N e).Adj :=
  Classical.decRel _

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
