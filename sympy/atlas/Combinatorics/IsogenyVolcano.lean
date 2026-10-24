/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Isogeny volcanoes on multigraphs

This file defines symmetric multigraphs by edge multiplicity and the combinatorial structure of
an isogeny volcano. Loops are permitted. The degree counts a loop's multiplicity once, following
the outgoing-isogeny convention rather than the convention where an undirected loop counts twice.
-/

set_option autoImplicit false

open BigOperators

/-- A multigraph described by a symmetric edge-multiplicity function. Loops are permitted. -/
structure Multigraph (V : Type*) where
  /-- The multiplicity of edges between two vertices. -/
  edgeMult : V → V → ℕ
  /-- Edge multiplicity is symmetric. -/
  symm : ∀ v w, edgeMult v w = edgeMult w v

namespace Multigraph

variable {V : Type*}

/-- Adjacency in a multigraph means positive edge multiplicity. -/
def Adj (G : Multigraph V) (v w : V) : Prop :=
  0 < G.edgeMult v w

/--
The outgoing degree of a vertex. A loop contributes its multiplicity once, matching the
outgoing-isogeny convention.
-/
def degree (G : Multigraph V) [Fintype V] (v : V) : ℕ :=
  ∑ w : V, G.edgeMult v w

/-- Degree restricted to vertices satisfying `P`. -/
def degreeOn (G : Multigraph V) [Fintype V] (v : V)
    (P : V → Prop) [DecidablePred P] : ℕ :=
  ∑ w ∈ Finset.univ.filter P, G.edgeMult v w

/-- Connectivity via reflexive-transitive closure. -/
def Connected (G : Multigraph V) (v w : V) : Prop :=
  Relation.ReflTransGen G.Adj v w

/-- A multigraph is connected when all pairs connect. -/
def IsConnected (G : Multigraph V) : Prop :=
  ∀ v w, G.Connected v w

/-- Every vertex connects to itself. -/
theorem connected_refl (G : Multigraph V) (v : V) :
    G.Connected v v :=
  Relation.ReflTransGen.refl
end Multigraph

/-- An `ℓ`-isogeny volcano with `Fin` levels, for prime `ℓ`. -/
structure IsogenyVolcano (ℓ : ℕ) where
  /-- The isogeny degree is prime. -/
  prime : Nat.Prime ℓ
  /-- Vertex type. -/
  V : Type*
  /-- Finite vertices. -/
  instFintype : Fintype V
  /-- Decidable equality on vertices. -/
  instDecEq : DecidableEq V
  /-- Underlying multigraph. -/
  graph : Multigraph V
  /-- Depth of the volcano. -/
  depth : ℕ
  /-- Level of each vertex. -/
  level : V → Fin (depth + 1)
  /-- Every level is inhabited. -/
  level_surj : Function.Surjective level
  /-- Surface degree. -/
  surfaceDegree : ℕ
  /-- Surface degree is at most two. -/
  surfaceDegree_le : surfaceDegree ≤ 2
  /-- Surface regularity. -/
  surface_regular : ∀ v,
    level v = ⟨0, Nat.zero_lt_succ _⟩ →
      graph.degreeOn v
        (fun w => level w = ⟨0, Nat.zero_lt_succ _⟩) =
        surfaceDegree
  /-- Every nonsurface vertex has a unique parent. -/
  unique_parent : ∀ v, (level v : ℕ) > 0 →
    graph.degreeOn v
      (fun w => (level w : ℕ) + 1 = (level v : ℕ)) = 1
  /-- Positive edges stay within or across adjacent levels. -/
  edges_between_levels : ∀ v w, graph.edgeMult v w > 0 →
    ((level v : ℕ) = 0 ∧ (level w : ℕ) = 0) ∨
      (level w : ℕ) + 1 = (level v : ℕ) ∨
        (level v : ℕ) + 1 = (level w : ℕ)
  /-- Regularity below the floor. -/
  degree_eq : ∀ v, (level v : ℕ) < depth →
    graph.degree v = ℓ + 1
  /-- The graph is connected. -/
  connected : graph.IsConnected

instance {ℓ : ℕ} (C : IsogenyVolcano ℓ) : Fintype C.V :=
  C.instFintype

instance {ℓ : ℕ} (C : IsogenyVolcano ℓ) : DecidableEq C.V :=
  C.instDecEq

namespace IsogenyVolcano

variable {ℓ : ℕ} {C : IsogenyVolcano ℓ}

/-- Surface vertices. -/
def isSurface (C : IsogenyVolcano ℓ) (v : C.V) : Prop :=
  C.level v = 0

/-- Floor vertices. -/
def isFloor (C : IsogenyVolcano ℓ) (v : C.V) : Prop :=
  C.level v = Fin.last C.depth

/-- Depth of the volcano. -/
def volcanoDepth (C : IsogenyVolcano ℓ) : ℕ :=
  C.depth

/-- Horizontal edge on the surface. -/
def IsHorizontalEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level v : ℕ) = 0 ∧ (C.level w : ℕ) = 0

/-- Descending edge from `v` down to `w`. -/
def IsDescendingEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level v : ℕ) + 1 = (C.level w : ℕ)

/-- An ascending edge from `v` to `w`, where `w` lies one level above `v`. -/
def IsAscendingEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.graph.edgeMult v w > 0 ∧
    (C.level w : ℕ) + 1 = (C.level v : ℕ)

/-- Vertical edge in either direction. -/
def IsVerticalEdge (C : IsogenyVolcano ℓ)
    (v w : C.V) : Prop :=
  C.IsDescendingEdge v w ∨ C.IsAscendingEdge v w

instance decPredIsSurface (C : IsogenyVolcano ℓ) :
    DecidablePred C.isSurface :=
  fun v => inferInstanceAs (Decidable (C.level v = 0))
end IsogenyVolcano
