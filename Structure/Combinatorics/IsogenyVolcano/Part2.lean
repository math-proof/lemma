/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorem.Combinatorics.IsogenyVolcano
set_option autoImplicit false

open BigOperators

/-!
# Isogeny volcanoes on multigraphs

This file defines symmetric multigraphs by edge multiplicity and the combinatorial structure of
an isogeny volcano. Loops are permitted. The degree counts a loop's multiplicity once, following
the outgoing-isogeny convention rather than the convention where an undirected loop counts twice.
-/


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

