/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Theorem.Combinatorics.SimpleGraph.Frucht


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

def fruchtShift (N : ℕ) {G : Type*} [Group G] (a : G) :
    Equiv.Perm (G ⊕ (G × Fin N)) :=
  Equiv.sumCongr (Equiv.mulLeft a) (Equiv.prodCongr (Equiv.mulLeft a) (Equiv.refl (Fin N)))

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
