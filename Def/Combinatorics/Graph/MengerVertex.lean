/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MengerVertex.lean -/

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat


section

namespace MetaMathlibExt

/-- Capacity in the vertex-split network on `V × Bool` (`false` = entry,
`true` = exit): unit capacity on internal vertex arcs, `big` on `s`/`t`
vertex arcs and on arcs following graph edges, zero elsewhere. -/
def splitCap {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (big : ℕ) :
    (V × Bool) → (V × Bool) → ℕ
  | (u, false), (v, true) =>
      if u = v then (if u = s ∨ u = t then big else 1) else 0
  | (u, true), (v, false) =>
      if G.Adj u v then big else 0
  | _, _ => 0

/-- A feasible `ℕ`-flow in the split network: bounded by capacities,
conserved away from source/sink, with no inflow to the source and no
outflow from the sink. -/
def IsSplitFlow {V : Type*} [Fintype V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ) : Prop :=
  (∀ a b, f a b ≤ cap a b) ∧
  (∀ w, w ≠ S → w ≠ T → ∑ u : V × Bool, f u w = ∑ v : V × Bool, f w v) ∧
  (∀ v, f v S = 0) ∧
  (∀ v, f T v = 0)

/-- Flow value: outflow from the source. -/
def splitValue {V : Type*} [Fintype V] (S : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ) : ℕ :=
  ∑ v : V × Bool, f S v

/-- Cut capacity: total capacity of arcs leaving the set. -/
def splitCutCap {V : Type*} [Fintype V] [DecidableEq V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (C : Finset (V × Bool)) : ℕ :=
  ∑ u ∈ C, ∑ v ∈ Finset.univ \ C, cap u v

/-- Consecutive pair in a list, via indices. -/
def isListStep {W : Type*} (l : List W) (a b : W) : Prop :=
  ∃ i : ℕ, ∃ hi : i < l.length, ∃ hi1 : i + 1 < l.length,
    l[i]'hi = a ∧ l[i + 1]'hi1 = b

/-- Residual relation: forward along unsaturated arcs, backward along used arcs. -/
def splitResid {V : Type*} (cap : (V × Bool) → (V × Bool) → ℕ)
    (f : (V × Bool) → (V × Bool) → ℕ) : (V × Bool) → (V × Bool) → Prop :=
  fun a b => f a b < cap a b ∨ 0 < f b a

end MetaMathlibExt
end
