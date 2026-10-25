import Mathlib
import Inductive.Analysis.Misc.erdos_613
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-- Adjacency relation for the Pikhurko n=5 counterexample.

* Inside {name}`A1` and inside {name}`A2`: cliques.
* Between {name}`A1`–{name}`B1` and {name}`A2`–{name}`B2`: complete bipartite.
* Inside {name}`B1` and {name}`B2`: no edges.
* No edges between the two blocks {name}`A1`/{name}`B1` and {name}`A2`/{name}`B2`.
* {name}`apex` is connected to every non-{name}`apex` vertex. -/
def GAdj : V → V → Prop
| apex, apex => False
| apex, _    => True
| _,    apex => True
| A1 i, A1 j => i ≠ j
| A2 i, A2 j => i ≠ j
| A1 _, B1 _ => True
| B1 _, A1 _ => True
| A2 _, B2 _ => True
| B2 _, A2 _ => True
| _,    _    => False

/-- The graph {name}`G` on 16 vertices used for the n=5 counterexample. -/
def G : SimpleGraph V where
  Adj := GAdj
  symm := { symm := fun u v h => by cases u <;> cases v <;> grind [GAdj] }
  loopless := ⟨by intro v; cases v <;> simp [GAdj]⟩

end PikhurkoN5
