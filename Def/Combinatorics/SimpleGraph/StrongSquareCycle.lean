/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StrongSquareCycle.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Theorem.Combinatorics.SimpleGraph.Square
import Lemma.SimpleGraph.Square
/-!
# Rooted Hamiltonian cycles in graph squares
-/


namespace SimpleGraph

/-- A Hamiltonian cycle in the square whose two edges at `x` come from the original graph. -/
def HasStrongSquareCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) : Prop :=
  ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
    G.Adj x p.snd ∧ G.Adj p.penultimate x

end SimpleGraph
