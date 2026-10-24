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
private def splitCap {V : Type*} [DecidableEq V]
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
private def IsSplitFlow {V : Type*} [Fintype V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (S T : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ) : Prop :=
  (∀ a b, f a b ≤ cap a b) ∧
  (∀ w, w ≠ S → w ≠ T → ∑ u : V × Bool, f u w = ∑ v : V × Bool, f w v) ∧
  (∀ v, f v S = 0) ∧
  (∀ v, f T v = 0)

/-- Flow value: outflow from the source. -/
private def splitValue {V : Type*} [Fintype V] (S : V × Bool)
    (f : (V × Bool) → (V × Bool) → ℕ) : ℕ :=
  ∑ v : V × Bool, f S v

/-- Cut capacity: total capacity of arcs leaving the set. -/
private def splitCutCap {V : Type*} [Fintype V] [DecidableEq V]
    (cap : (V × Bool) → (V × Bool) → ℕ) (C : Finset (V × Bool)) : ℕ :=
  ∑ u ∈ C, ∑ v ∈ Finset.univ \ C, cap u v

/-- Consecutive pair in a list, via indices. -/
private def isListStep {W : Type*} (l : List W) (a b : W) : Prop :=
  ∃ i : ℕ, ∃ hi : i < l.length, ∃ hi1 : i + 1 < l.length,
    l[i]'hi = a ∧ l[i + 1]'hi1 = b

/-- Residual relation: forward along unsaturated arcs, backward along used arcs. -/
private def splitResid {V : Type*} (cap : (V × Bool) → (V × Bool) → ℕ)
    (f : (V × Bool) → (V × Bool) → ℕ) : (V × Bool) → (V × Bool) → Prop :=
  fun a b => f a b < cap a b ∨ 0 < f b a

private noncomputable instance decIsListStep {W : Type*} (l : List W) (a b : W) :
    Decidable (isListStep l a b) :=
  Classical.propDecidable _

/-- Augmented flow along a residual path: increment forward steps, decrement
backward steps (preferring forward when both apply). -/
private noncomputable def splitAugment {V : Type*}
    (cap : (V × Bool) → (V × Bool) → ℕ)
    (l : List (V × Bool)) (f : (V × Bool) → (V × Bool) → ℕ) :
    (V × Bool) → (V × Bool) → ℕ :=
  fun a b =>
    f a b
      + (if isListStep l a b ∧ f a b < cap a b then 1 else 0)
      - (if isListStep l b a ∧ ¬ f b a < cap b a then 1 else 0)

/-- Removing a path: decrement flow along list steps. -/
private noncomputable def splitRemove {V : Type*}
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
private def path_of_nodupWalk {V : Type*} {G : SimpleGraph V} {s t : V}
    (w : G.Walk s t) (h : w.support.Nodup) : G.Path s t :=
  ⟨w, SimpleGraph.Walk.IsPath.mk' h⟩
end MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted
end
