/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StrongSquareCycle.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import sympy.atlas.Combinatorics.SimpleGraph.Square
/-!
# Rooted Hamiltonian cycles in graph squares
-/

namespace SimpleGraph

/-- A Hamiltonian cycle in the square whose two edges at `x` come from the original graph. -/
def HasStrongSquareCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) : Prop :=
  ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
    G.Adj x p.snd ∧ G.Adj p.penultimate x

/-- A strong square cycle consists of a Hamiltonian cycle with original edges at the root. -/
theorem hasStrongSquareCycle_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) :
    G.HasStrongSquareCycle x ↔
      ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
        G.Adj x p.snd ∧ G.Adj p.penultimate x :=
  Iff.rfl

end SimpleGraph
