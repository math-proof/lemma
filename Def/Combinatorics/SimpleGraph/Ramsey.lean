/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ramsey.lean -/

/-
# Classical graph Ramsey numbers
-/

import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Nat
/-!
The arbitrary-graph Ramsey API is adapted from
`google-deepmind/formal-conjectures@62f56e8e4dab933a720f649721875c478b0ecf1c`,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`.
-/


namespace SimpleGraph

/-- `classicalRamsey s t N` says that every graph on `N` vertices contains an
ordinary copy of `K_s`, or its complement contains an ordinary copy of `K_t`.
Thus the graph and its complement encode the two colors of a complete graph. -/
def classicalRamsey (s t N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    IsContained (completeGraph (Fin s)) G ∨
      IsContained (completeGraph (Fin t)) Gᶜ

/-- The classical two-color graph Ramsey number `R(s, t)`, defined as the least
cardinality at which `classicalRamsey s t` holds.

The defining set is nonempty by the finite Ramsey theorem. This definition is
total independently of that fact because `sInf` on `ℕ` is total. -/
noncomputable def graphRamsey (s t : ℕ) : ℕ :=
  sInf {N : ℕ | classicalRamsey s t N}

/-- The two-color Ramsey number for an arbitrary pair of finite graphs. This
uses a separate name so the established natural-parameter `graphRamsey` API
remains compatible with existing callers. -/
noncomputable def graphPairRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ}

/-- The diagonal graph Ramsey number `R(G, G)` for an arbitrary finite graph. -/
noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphPairRamsey G G

/-- A graph `G` is Ramsey size linear if `R(G,H)` is bounded linearly by the
number of edges of every finite graph `H` without isolated vertices. -/
def IsRamseySizeLinear {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) →
    (graphPairRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

end SimpleGraph
