/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Interval.Finset.Fin
public import Def.Combinatorics.SimpleGraph.Frucht

@[expose] public section

section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

noncomputable instance fruchtGraphDec (N : ℕ) {G : Type*} [Group G] [DecidableEq G]
    [Fintype G] (e : G ≃ Fin N) : DecidableRel (fruchtGraph N e).Adj :=
  Classical.decRel _

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
