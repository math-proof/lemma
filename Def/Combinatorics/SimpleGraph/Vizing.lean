/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Vizing.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Def.Combinatorics.SimpleGraph.EdgeColoring
public import Theorem.Finset.SimpleGraph.EdgeColoring
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# Edge coloring landmarks

Records Vizing and König edge-coloring theorems.
-/


section

namespace MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted

-- `IsProperEdgeColoring` is imported from `EdgeColoring` in the same namespace.

/-- Properness for total colorings of unordered pairs (used to avoid
dependent `EdgeLabeling` domains while the graph changes). -/
def IsProperSym2Coloring {V K : Type*} (G : _root_.SimpleGraph V) (c : Sym2 V → K) : Prop :=
  ∀ {x y z : V}, G.Adj x y → G.Adj x z → y ≠ z → c s(x, y) ≠ c s(x, z)

/-- Colors missing at a vertex. -/
noncomputable def missingColors {V K : Type*} [Fintype K] [DecidableEq K]
    (G : _root_.SimpleGraph V)
    (c : Sym2 V → K) (u : V) : Finset K := by
  classical
  exact Finset.univ.filter (fun i => ∀ (y : V), G.Adj u y → c s(u, y) ≠ i)

/-- Kempe swap: swap colors α β on pairs fully inside S. -/
noncomputable def kempeSwap {V K : Type*} [DecidableEq K]
    (c : Sym2 V → K) (α β : K) (S : Set V) : Sym2 V → K :=
  open Classical in
  fun e => if ∀ x ∈ e, x ∈ S then Equiv.swap α β (c e) else c e

/-- The subgraph of `G` formed by edges colored `α` or `β`. -/
def kempeGraph {V K : Type*} [DecidableEq K]
    (G : _root_.SimpleGraph V) (c : Sym2 V → K) (α β : K) : _root_.SimpleGraph V :=
  G.deleteEdges { e | c e ≠ α ∧ c e ≠ β }

end MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted
end
