import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.HamiltonianCycle
open SimpleGraph


/--
[IsHamiltonian.of_cyclic_list](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HamiltonianCycle.lean)
-/
@[path]
private lemma IsHamiltonian_of_cyclic_list_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}
  {l : List V}
-- given
  (hne : l ≠ [])
  (hclosed : l.head hne = l.getLast hne)
  (hchain : l.IsChain G.Adj)
  (hnodup : l.tail.Nodup)
  (hmem : ∀ v, v ∈ l.tail)
  (hthree : 3 ≤ l.length - 1) :
-- imply
  G.IsHamiltonian := by
-- proof
  apply SimpleGraph.IsHamiltonian.of_cyclic_list G l hne hclosed hchain hnodup hmem hthree


-- created on 2026-10-20
