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

/-- Adjacency is symmetric. -/
theorem adj_comm (G : Multigraph V) (v w : V) :
    G.Adj v w ↔ G.Adj w v := by
  unfold Adj
  rw [G.symm v w]

/-- Every vertex connects to itself. -/
theorem connected_refl (G : Multigraph V) (v : V) :
    G.Connected v v :=
  Relation.ReflTransGen.refl

/-- Degree splits over a predicate and its complement. -/
theorem degreeOn_compl (G : Multigraph V) [Fintype V]
    (v : V) (P : V → Prop) [DecidablePred P] :
    G.degree v = G.degreeOn v P + G.degreeOn v (fun w => ¬ P w) := by
  unfold degree degreeOn
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ P _).symm

/-- `degreeOn` depends only on predicate values on support. -/
theorem degreeOn_congr (G : Multigraph V) [Fintype V]
    (v : V) {P Q : V → Prop}
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ w, G.edgeMult v w > 0 → (P w ↔ Q w)) :
    G.degreeOn v P = G.degreeOn v Q := by
  unfold degreeOn
  have hsubP :
      Finset.univ.filter (fun w => P w ∧ Q w) ⊆
        Finset.univ.filter P := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx.1
  have hsubQ :
      Finset.univ.filter (fun w => P w ∧ Q w) ⊆
        Finset.univ.filter Q := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx.2
  have hzP : ∀ x ∈ Finset.univ.filter P,
      x ∉ Finset.univ.filter (fun w => P w ∧ Q w) →
        G.edgeMult v x = 0 := by
    intro x hxP hxN
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hxP hxN
    have hNQ : ¬ Q x := fun hQx => hxN ⟨hxP, hQx⟩
    by_contra hne
    have hpos : G.edgeMult v x > 0 :=
      Nat.pos_of_ne_zero hne
    exact hNQ ((h x hpos).mp hxP)
  have hzQ : ∀ x ∈ Finset.univ.filter Q,
      x ∉ Finset.univ.filter (fun w => P w ∧ Q w) →
        G.edgeMult v x = 0 := by
    intro x hxQ hxN
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at hxQ hxN
    have hNP : ¬ P x := fun hPx => hxN ⟨hPx, hxQ⟩
    by_contra hne
    have hpos : G.edgeMult v x > 0 :=
      Nat.pos_of_ne_zero hne
    exact hNP ((h x hpos).mpr hxQ)
  have eP := Finset.sum_subset hsubP hzP
  have eQ := Finset.sum_subset hsubQ hzQ
  rw [← eP, ← eQ]

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

/-- Descending is ascending with swapped endpoints. -/
theorem descending_iff_ascending_symm (v w : C.V) :
    C.IsDescendingEdge v w ↔ C.IsAscendingEdge w v := by
  simp only [IsDescendingEdge, IsAscendingEdge]
  constructor
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rw [← C.graph.symm v w]
    exact hpos
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rw [C.graph.symm v w]
    exact hpos

/-- Ascending is descending with swapped endpoints. -/
theorem ascending_iff_descending_symm (v w : C.V) :
    C.IsAscendingEdge v w ↔ C.IsDescendingEdge w v := by
  simp only [IsAscendingEdge, IsDescendingEdge]
  constructor
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rw [← C.graph.symm v w]
    exact hpos
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rw [C.graph.symm v w]
    exact hpos

/-- Every positive edge has a direction. -/
theorem edge_direction (v w : C.V)
    (h : C.graph.edgeMult v w > 0) :
    C.IsHorizontalEdge v w ∨ C.IsDescendingEdge v w ∨
      C.IsAscendingEdge v w := by
  rcases C.edges_between_levels v w h with
    ⟨hv0, hw0⟩ | hdesc | hasc
  · exact Or.inl ⟨h, hv0, hw0⟩
  · exact Or.inr (Or.inr ⟨h, hdesc⟩)
  · exact Or.inr (Or.inl ⟨h, hasc⟩)

/-- Surface means level value zero. -/
@[simp] theorem isSurface_iff (v : C.V) :
    C.isSurface v ↔ (C.level v : ℕ) = 0 := by
  change C.level v = (0 : Fin (C.depth + 1)) ↔ (C.level v : ℕ) = 0
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    exact Fin.ext h

/-- Floor means level value equals depth. -/
@[simp] theorem isFloor_iff (v : C.V) :
    C.isFloor v ↔ (C.level v : ℕ) = C.depth := by
  unfold isFloor
  constructor
  · intro h; rw [h]; simp
  · intro h; apply Fin.ext; simpa [Fin.val_last] using h

/-- Surface regularity via surface predicates. -/
@[simp] theorem surface_degreeOn (v : C.V) (hv : C.isSurface v) :
    C.graph.degreeOn v (fun w => C.isSurface w) = C.surfaceDegree := by
  have hv0 : C.level v = ⟨0, Nat.zero_lt_succ _⟩ := by
    exact Fin.ext ((C.isSurface_iff v).mp hv)
  calc
    C.graph.degreeOn v (fun w => C.isSurface w) =
        C.graph.degreeOn v
          (fun w => C.level w = ⟨0, Nat.zero_lt_succ _⟩) := by
      apply C.graph.degreeOn_congr
      intro w _
      constructor
      · intro hw
        exact Fin.ext ((C.isSurface_iff w).mp hw)
      · intro hw
        apply (C.isSurface_iff w).mpr
        exact congrArg Fin.val hw
    _ = C.surfaceDegree := C.surface_regular v hv0

end IsogenyVolcano
