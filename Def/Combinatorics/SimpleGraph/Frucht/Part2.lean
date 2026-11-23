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
public import Theorem.Combinatorics.SimpleGraph.Frucht

@[expose] public section

section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

def fruchtShift (N : ℕ) {G : Type*} [Group G] (a : G) :
    Equiv.Perm (G ⊕ (G × Fin N)) :=
  Equiv.sumCongr (Equiv.mulLeft a) (Equiv.prodCongr (Equiv.mulLeft a) (Equiv.refl (Fin N)))

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
