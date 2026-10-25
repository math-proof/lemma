/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MengerVertex.lean -/

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat
import Instance.Combinatorics.Graph.MengerVertex


section

namespace MetaMathlibExt

/-- Augmented flow along a residual path: increment forward steps, decrement
backward steps (preferring forward when both apply). -/
noncomputable def splitAugment {V : Type*}
    (cap : (V × Bool) → (V × Bool) → ℕ)
    (l : List (V × Bool)) (f : (V × Bool) → (V × Bool) → ℕ) :
    (V × Bool) → (V × Bool) → ℕ :=
  fun a b =>
    f a b
      + (if isListStep l a b ∧ f a b < cap a b then 1 else 0)
      - (if isListStep l b a ∧ ¬ f b a < cap b a then 1 else 0)

/-- Removing a path: decrement flow along list steps. -/
noncomputable def splitRemove {V : Type*}
    (l : List (V × Bool)) (f : (V × Bool) → (V × Bool) → ℕ) :
    (V × Bool) → (V × Bool) → ℕ :=
  fun a b => f a b - (if isListStep l a b then 1 else 0)

end MetaMathlibExt

namespace MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted

/-
Adapted from `WantedExt/Combinatorics/SimpleGraph/MengerVertexWanted.lean`: the
definitions `IsInternallyVertexDisjointSTPaths` and `IsSTVertexCut`, and the statement
of `menger_vertex_max_min`, follow the API proposed there, originally contributed by
`@toskua, Avocado`. All proofs given here are new.
-/

/-- Internally vertex-disjoint `s-t` paths: common vertex of distinct paths is `s` or `t`. -/
def IsInternallyVertexDisjointSTPaths {V : Type*} {G : SimpleGraph V}
    {s t : V} {n : ℕ} (paths : Fin n → G.Path s t) : Prop :=
  ∀ i j, i ≠ j → ∀ v, v ∈ (paths i).val.support →
    v ∈ (paths j).val.support → v = s ∨ v = t

/-- `s-t` vertex cut: `s ∉ C`, `t ∉ C`, and deleting `C` disconnects `s` from `t`. -/
def IsSTVertexCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (C : Finset V) : Prop :=
  s ∉ C ∧ t ∉ C ∧
    ¬ (((⊤ : G.Subgraph).deleteVerts (↑C : Set V)).spanningCoe.Reachable s t)

/-- Every walk with a nodup vertex list is a path. -/
def path_of_nodupWalk {V : Type*} {G : SimpleGraph V} {s t : V}
    (w : G.Walk s t) (h : w.support.Nodup) : G.Path s t :=
  ⟨w, SimpleGraph.Walk.IsPath.mk' h⟩

end MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted
end
