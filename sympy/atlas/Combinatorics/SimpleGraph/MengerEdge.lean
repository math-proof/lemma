/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MengerEdge.lean -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

section
namespace MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted

/-! # Finite Menger theorem (edge form)

Proves the edge version of Menger's theorem for finite simple graphs: the maximum number of
pairwise edge-disjoint `s-t` paths equals the minimum size of an `s-t` edge cut.
-/

/-- Family `paths` of `s-t` paths is edge-disjoint when distinct paths share no edge. -/
def IsEdgeDisjointSTPaths {V : Type*} {G : SimpleGraph V}
    {s t : V} {n : ℕ} (paths : Fin n → G.Path s t) : Prop :=
  ∀ i j, i ≠ j → ∀ e : Sym2 V, e ∈ (paths i).val.edges → e ∉ (paths j).val.edges

/-- `C` is an `s-t` edge cut when `C ⊆ G.edgeSet` and deleting `C` disconnects `s` from `t`. -/
def IsSTEdgeCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (C : Finset (Sym2 V)) : Prop :=
  (↑C : Set (Sym2 V)) ⊆ G.edgeSet ∧ ¬ (G.deleteEdges (↑C : Set (Sym2 V))).Reachable s t

/-- Ordered pairs used by a family of paths. -/
private def UsedPairs {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) : Set (V × V) :=
  {p | ∃ i, ∃ d ∈ (paths i).val.darts, d.toProd = p}

/-- Residual relation: `G`-edges whose forward dart is unused. -/
private def ResidualRel {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) : V → V → Prop :=
  fun a b => G.Adj a b ∧ (a, b) ∉ UsedPairs paths

/-- Vertices reachable from `s` in the residual relation. -/
private def ResidReachableSet {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) : Set V :=
  {v | Relation.ReflTransGen (ResidualRel paths) s v}

/-- An edge crosses the residual cut when it joins `S` to its complement. -/
private def IsCrossing {V : Type*} {G : SimpleGraph V} {s t : V} {k : ℕ}
    (paths : Fin k → G.Path s t) (e : Sym2 V) : Prop :=
  ∃ a b, e = s(a, b) ∧
    ((a ∈ ResidReachableSet paths ∧ b ∉ ResidReachableSet paths) ∨
      (a ∉ ResidReachableSet paths ∧ b ∈ ResidReachableSet paths))

/-- Outgoing dart count of `v` in `D`. -/
private def outCount {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (D : Finset G.Dart) (v : V) : ℕ :=
  (D.filter (fun d => d.fst = v)).card

/-- Incoming dart count of `v` in `D`. -/
private def inCount {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (D : Finset G.Dart) (v : V) : ℕ :=
  (D.filter (fun d => d.snd = v)).card

/-- All darts of `paths` plus `q`. -/
private def D0Finset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) (q : G.Path s t) :
    Finset G.Dart :=
  (Finset.univ.biUnion (fun i => (paths i).val.darts.toFinset)) ∪
    q.val.darts.toFinset

/-- Darts of `D0` with opposite present (to cancel). -/
private def CancelFinset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) (q : G.Path s t) :
    Finset G.Dart :=
  (D0Finset paths q).filter (fun d => d.symm ∈ D0Finset paths q)

/-- Remaining darts after cancelling opposite pairs. -/
private def DFinset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {k : ℕ} (paths : Fin k → G.Path s t) (q : G.Path s t) :
    Finset G.Dart :=
  (D0Finset paths q) \ (CancelFinset paths q)

/-- Flow balance: `D` carries `n` units of flow from `s` to `t`. -/
private def Balances {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (s t : V) (D : Finset G.Dart) (n : ℕ) : Prop :=
  ∀ x : V, outCount D x + (if x = t then n else 0) =
    inCount D x + (if x = s then n else 0)
end MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted
end
