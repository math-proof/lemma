import Mathlib
import sympy.Basic
import Instance.Combinatorics.IsogenyVolcano.Part2
open BigOperators
open Multigraph
open IsogenyVolcano


namespace Multigraph


namespace Multigraph.IsogenyVolcano

/--
[descending_iff_ascending_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
lemma descending_iff_ascending_symm
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v w : C.V} :
-- imply
  C.IsDescendingEdge v w ↔ C.IsAscendingEdge w v := by
-- proof
  simp only [IsDescendingEdge, IsAscendingEdge]
  constructor
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rwa [← C.graph.symm v w]
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rwa [C.graph.symm v w]

end Multigraph.IsogenyVolcano

namespace Multigraph.IsogenyVolcano

/--
[edge_direction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
lemma edge_direction
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v w : C.V}
-- given
  (h : C.graph.edgeMult v w > 0) :
-- imply
  C.IsHorizontalEdge v w ∨ C.IsDescendingEdge v w ∨
    C.IsAscendingEdge v w := by
-- proof
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

end Multigraph.IsogenyVolcano

/--
[adj_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
lemma adj_comm
  {G : Multigraph V}
  {v w : V} :
-- imply
  G.Adj v w ↔ G.Adj w v := by
-- proof
  unfold Adj
  rw [G.symm v w]

end Multigraph

namespace Multigraph

/--
[degreeOn_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
lemma degreeOn_compl
  [Fintype V] [DecidablePred P]
  {G : Multigraph V}
  {v : V}
-- given
  (P : V → Prop) :
-- imply
  G.degree v = G.degreeOn v P + G.degreeOn v (fun w => ¬ P w) := by
-- proof
  unfold degree degreeOn
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ P _).symm

end Multigraph

namespace Multigraph

/--
[degreeOn_congr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
lemma degreeOn_congr
  [Fintype V]
  {G : Multigraph V}
  {v : V}
  {P Q : V → Prop} [DecidablePred P] [DecidablePred Q]
-- given
  (h : ∀ w, G.edgeMult v w > 0 → (P w ↔ Q w)) :
-- imply
  G.degreeOn v P = G.degreeOn v Q := by
-- proof
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

namespace IsogenyVolcano

/--
[ascending_iff_descending_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
lemma ascending_iff_descending_symm
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v w : C.V} :
-- imply
  C.IsAscendingEdge v w ↔ C.IsDescendingEdge w v := by
-- proof
  simp only [IsAscendingEdge, IsDescendingEdge]
  constructor
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rwa [← C.graph.symm v w]
  · rintro ⟨hpos, hlev⟩
    refine ⟨?_, hlev⟩
    rwa [C.graph.symm v w]

end IsogenyVolcano

/--
[connected_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma connected_refl_eq
  {G : Multigraph V}
  {v : V} :
-- imply
  G.Connected v v := by
-- proof
  apply Multigraph.connected_refl G v

/--
[isSurface_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma isSurface_iff_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v : C.V} :
-- imply
  C.isSurface v ↔ (C.level v : ℕ) = 0 := by
-- proof
  apply IsogenyVolcano.isSurface_iff v

/--
[isFloor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma isFloor_iff_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v : C.V} :
-- imply
  C.isFloor v ↔ (C.level v : ℕ) = C.depth := by
-- proof
  apply IsogenyVolcano.isFloor_iff v

/--
[surface_degreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma surface_degreeOn_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v : C.V}
-- given
  (hv : C.isSurface v) :
-- imply
  C.graph.degreeOn v (fun w => C.isSurface w) = C.surfaceDegree := by
-- proof
  apply IsogenyVolcano.surface_degreeOn v hv


-- created on 2026-10-20
-- updated on 2026-10-23
