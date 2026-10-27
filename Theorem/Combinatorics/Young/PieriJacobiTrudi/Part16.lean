/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part29
import Def.Combinatorics.Young.OmegaInvolution.Part2
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Lemma.Matrix.LGV2
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.PieriJacobiTrudi.Part29
open Finset BigOperators Matrix MvPolynomial

/-!
# The Pieri Rules and Jacobi-Trudi Identities

This file formalizes the Pieri rules for multiplying Schur polynomials by complete
homogeneous or elementary symmetric polynomials, and the Jacobi-Trudi identities
expressing skew Schur polynomials as determinants.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of nonnegative integers
* `NPartition.IsTranspose`: Predicate asserting that two partitions are transposes
* `SkewPartition`: A skew partition λ/μ is a pair of partitions with μ ⊆ λ
* `SkewPartition.isHorizontalStrip`: A skew partition is a horizontal strip if no two
  boxes in Y(λ/μ) lie in the same column
* `SkewPartition.isVerticalStrip`: A skew partition is a vertical strip if no two
  boxes in Y(λ/μ) lie in the same row
* `SkewPartition.isHorizontalNStrip`: A horizontal n-strip has exactly n boxes
* `SkewPartition.isVerticalNStrip`: A vertical n-strip has exactly n boxes
* `isHorizontalStripFun`: Canonical unbundled horizontal strip predicate with `(lam, mu)` order
* `isVerticalStripFun`: Canonical unbundled vertical strip predicate with `(lam, mu)` order
* `SSYT`: A semistandard Young tableau of shape λ
* `SkewSSYT`: A semistandard Young tableau of skew shape λ/μ
* `LatticePath`: A lattice path in ℤ² using north and east steps
* `Nipat`: A non-intersecting path tuple (for LGV lemma connection)

## Main results

* `pieri_horizontal`: h_n · s_μ = ∑_{λ/μ is horizontal n-strip} s_λ (Theorem thm.sf.pieri(a))
* `pieri_vertical`: e_n · s_μ = ∑_{λ/μ is vertical n-strip} s_λ (Theorem thm.sf.pieri(b))
* `horizontalStrip_iff_entries`: Characterization of horizontal strips via partition entries
    (Proposition prop.sf.strips.entries(a))
* `verticalStrip_iff_entries`: Characterization of vertical strips via partition entries
    (Proposition prop.sf.strips.entries(b))
* `jacobiTrudi_h`: s_{λ/μ} = det(h_{λᵢ - μⱼ - i + j}) (Theorem thm.sf.jt-h)
* `jacobiTrudi_e`: s_{λ/μ} = det(e_{λᵢᵗ - μⱼᵗ - i + j}) (Theorem thm.sf.jt-e)

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex
* [Stanley, *Enumerative Combinatorics, Vol. 2*][Stanley-EC2]
* [Grinberg-Reiner, *Hopf algebras in combinatorics*][GriRei]

## Implementation notes

We work with N-partitions as length-N lists of weakly decreasing nonnegative integers.
Schur polynomials are defined via semistandard Young tableaux (SSYT).
The Jacobi-Trudi identities are proved using the Lindström-Gessel-Viennot lemma
(see AlgebraicCombinatorics/Determinants/LGV2.lean).

For h_n and e_n with negative n, we use the convention h_n = 0 and e_n = 0.

Note: In the source, M is the length of the partition tuples (for Jacobi-Trudi),
while N is the number of variables (entries in tableaux come from [N]).
We use a single parameter N for simplicity in this formalization.

### Strip Definition Conventions

There are three representations for horizontal/vertical strip predicates:

1. **Bundled (`SkewPartition.isHorizontalStrip`)**: Takes a `SkewPartition N` directly.
   Use when working with bundled skew partitions.

2. **Unbundled canonical (`isHorizontalStripFun`)**: Takes `(lam mu : Fin N → ℕ)` with
   argument order matching the mathematical notation λ/μ. **Preferred for new code.**

See `SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun` for the equivalence lemma.
-/


namespace SymmetricFunctions

variable {N : ℕ} {R : Type*} [CommRing R]

/-- Helper: x-coordinate is monotone along a path in the integer lattice -/
theorem x_coord_monotone_along_path (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (h_ne : vertices ≠ []) :
    (vertices.head h_ne).1 ≤ (vertices.getLast h_ne).1 := by
  induction vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ vs ih =>
    cases vs with
    | nil => simp
    | cons v₁ rest =>
      have h_arc : LGV.integerLattice.arc v₀ v₁ := by
        have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
        simp at this
        exact this
      have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
            ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
        have := h_arcs (i + 1) hi'
        simp at this ⊢
        exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest
      have ih' := ih h_arcs' h_ne'
      simp only [List.head_cons, List.getLast_cons h_ne'] at ih' ⊢
      -- v₀.1 ≤ v₁.1 from the arc, and v₁.1 ≤ getLast.1 from IH
      rcases h_arc with ⟨hx, _⟩ | ⟨hx, _⟩
      · -- East-step: v₁.1 = v₀.1 + 1
        omega
      · -- North-step: v₁.1 = v₀.1
        omega

/-- The number of east-steps equals the x-displacement.
    This is a key property for the bijection. -/
theorem lgvPathEastStepYCoords_length_eq_xDisplacement (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩)) :
    (lgvPathEastStepYCoords vertices).length =
      ((vertices.getLast h_ne).1 - (vertices.head h_ne).1).toNat := by
  -- Each east-step increases x by 1, north-steps don't change x
  -- So total east-steps = final x - initial x
  induction vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ vs ih =>
    cases vs with
    | nil =>
      simp [lgvPathEastStepYCoords]
    | cons v₁ rest =>
      have h_arc : LGV.integerLattice.arc v₀ v₁ := by
        have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
        simp at this
        exact this
      have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
            ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
        have := h_arcs (i + 1) hi'
        simp at this ⊢
        exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest
      have ih' := ih h_ne' h_arcs'
      -- Get the monotonicity bound for toNat
      have h_mono := x_coord_monotone_along_path (v₁ :: rest) h_arcs' h_ne'
      simp only [List.head_cons] at h_mono
      simp only [lgvPathEastStepYCoords]
      rcases h_arc with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · -- East-step: v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2
        simp only [hx, hy, and_self, ↓reduceIte, List.length_cons]
        rw [ih']
        simp only [List.head_cons, List.getLast_cons h_ne']
        -- Need: (getLast.1 - v₁.1).toNat + 1 = (getLast.1 - v₀.1).toNat
        -- where v₁.1 = v₀.1 + 1
        -- From h_mono: v₁.1 ≤ getLast.1, i.e., v₀.1 + 1 ≤ getLast.1
        omega
      · -- North-step: v₁.1 = v₀.1 ∧ v₁.2 = v₀.2 + 1
        have h_not_east : ¬(v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2) := by omega
        simp only [h_not_east, ↓reduceIte]
        rw [ih']
        simp only [List.head_cons, List.getLast_cons h_ne']
        -- Since v₁.1 = v₀.1, the toNat expressions are equal
        congr 1
        omega

/-- Helper lemma: y-coordinates are non-decreasing along any path in the integer lattice. -/
theorem lgvPath_y_nondecreasing (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (i j : ℕ) (hi : i < vertices.length) (hj : j < vertices.length) (hij : i ≤ j) :
    (vertices.get ⟨i, hi⟩).2 ≤ (vertices.get ⟨j, hj⟩).2 := by
  induction j with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · rfl
    · have hk : k < vertices.length := Nat.lt_of_succ_lt hj
      have hik' : i ≤ k := Nat.lt_succ_iff.mp hik
      have h1 := ih hk hik'
      have harc := h_arcs k hj
      simp only [LGV.integerLattice] at harc
      rcases harc with ⟨_, hy⟩ | ⟨_, hy⟩ <;> omega

/-- Helper lemma: all y-coordinates in lgvPathEastStepYCoords are y-coordinates of vertices. -/
theorem lgvPathEastStepYCoords_mem (vertices : List (ℤ × ℤ)) (y : ℤ)
    (hy : y ∈ lgvPathEastStepYCoords vertices) :
    ∃ i : ℕ, ∃ hi : i < vertices.length, (vertices.get ⟨i, hi⟩).2 = y := by
  induction vertices with
  | nil => simp [lgvPathEastStepYCoords] at hy
  | cons v₀ tl ih =>
    cases tl with
    | nil => simp [lgvPathEastStepYCoords] at hy
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords] at hy
      split_ifs at hy with h_east
      · cases hy with
        | head =>
          exact ⟨0, by simp, rfl⟩
        | tail _ hmem =>
          obtain ⟨i, hi, heq⟩ := ih hmem
          simp only [List.length_cons] at hi
          have hi' : i + 1 < (v₀ :: v₁ :: rest).length := by simp; omega
          refine ⟨i + 1, hi', ?_⟩
          simp only [List.get_eq_getElem]
          have : (v₀ :: v₁ :: rest)[i + 1]'hi' = (v₁ :: rest)[i]'hi := by simp
          rw [this, ← heq]
          simp [List.get_eq_getElem]
      · obtain ⟨i, hi, heq⟩ := ih hy
        simp only [List.length_cons] at hi
        have hi' : i + 1 < (v₀ :: v₁ :: rest).length := by simp; omega
        refine ⟨i + 1, hi', ?_⟩
        simp only [List.get_eq_getElem]
        have : (v₀ :: v₁ :: rest)[i + 1]'hi' = (v₁ :: rest)[i]'hi := by simp
        rw [this, ← heq]
        simp [List.get_eq_getElem]

/-- Helper lemma: head of lgvPathEastStepYCoords is a y-coordinate of some vertex. -/
theorem lgvPathEastStepYCoords_head_mem (vertices : List (ℤ × ℤ)) (y : ℤ)
    (hy : y ∈ (lgvPathEastStepYCoords vertices).head?) :
    ∃ i : ℕ, ∃ hi : i < vertices.length, (vertices.get ⟨i, hi⟩).2 = y := by
  have hmem : y ∈ lgvPathEastStepYCoords vertices := by
    cases h : lgvPathEastStepYCoords vertices with
    | nil => simp [h] at hy
    | cons hd tl => simp [h] at hy; rw [hy]; simp
  exact lgvPathEastStepYCoords_mem vertices y hmem

/-- East-step y-coordinates are weakly increasing (paths go north or east). -/
theorem lgvPathEastStepYCoords_weaklyIncreasing (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩)) :
    (lgvPathEastStepYCoords vertices).IsChain (· ≤ ·) := by
  -- The proof proceeds by induction on the vertex list.
  -- For each east-step, we show its y-coordinate is ≤ the next east-step's y-coordinate
  -- because y can only increase (north-steps) or stay the same (east-steps) along the path.
  induction vertices with
  | nil => exact List.isChain_nil
  | cons v₀ tl ih =>
    cases tl with
    | nil => exact List.isChain_nil
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords]
      split_ifs with h_east
      · -- v₀ → v₁ is an east-step
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
            LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
          exact h_arcs (i + 1) hi'
        have ih' := ih h_arcs'
        rw [List.isChain_cons]
        constructor
        · -- Show v₀.2 ≤ head of lgvPathEastStepYCoords (v₁ :: rest)
          intro y hy
          obtain ⟨i, hi, heq⟩ := lgvPathEastStepYCoords_head_mem (v₁ :: rest) y hy
          -- v₀.2 = v₁.2 (from east-step) and v₁.2 ≤ (v₁ :: rest)[i].2 by monotonicity
          have hv01 : v₀.2 = v₁.2 := h_east.2.symm
          have hmono := lgvPath_y_nondecreasing (v₁ :: rest) h_arcs' 0 i (by simp) hi (Nat.zero_le _)
          simp at hmono
          rw [hv01, ← heq]
          exact hmono
        · exact ih'
      · -- v₀ → v₁ is a north-step, so the result is just lgvPathEastStepYCoords (v₁ :: rest)
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
            LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
          exact h_arcs (i + 1) hi'
        exact ih h_arcs'

/-- East-step y-coordinates are bounded between start and end y-coordinates. -/
theorem lgvPathEastStepYCoords_bounded (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (y : ℤ) (hy : y ∈ lgvPathEastStepYCoords vertices) :
    (vertices.head h_ne).2 ≤ y ∧ y ≤ (vertices.getLast h_ne).2 := by
  -- y is a y-coordinate of some vertex
  obtain ⟨i, hi, heq⟩ := lgvPathEastStepYCoords_mem vertices y hy
  constructor
  · -- head.2 ≤ y
    have h_head : (vertices.head h_ne).2 = (vertices.get ⟨0, List.length_pos_of_ne_nil h_ne⟩).2 := by
      simp [List.head_eq_getElem]
    rw [h_head, ← heq]
    exact lgvPath_y_nondecreasing vertices h_arcs 0 i (List.length_pos_of_ne_nil h_ne) hi (Nat.zero_le _)
  · -- y ≤ getLast.2
    have h_last : (vertices.getLast h_ne).2 =
        (vertices.get ⟨vertices.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil h_ne) Nat.one_pos⟩).2 := by
      simp [List.getLast_eq_getElem]
    rw [h_last, ← heq]
    have hlen : vertices.length - 1 < vertices.length := Nat.sub_lt (List.length_pos_of_ne_nil h_ne) Nat.one_pos
    have hi_le : i ≤ vertices.length - 1 := by omega
    exact lgvPath_y_nondecreasing vertices h_arcs i (vertices.length - 1) hi hlen hi_le

/-- Auxiliary lemma: the k-th element of lgvPathEastStepYCoords corresponds to a vertex
    at x-coordinate start_x + k, AND that vertex is the start of an east step.
    This is the core induction for lgvPathEastStepYCoords_at_x. -/
theorem lgvPathEastStepYCoords_at_x_aux (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords vertices).length) :
    ∃ (idx : ℕ) (hidx : idx < vertices.length),
      (vertices.get ⟨idx, hidx⟩).1 = (vertices.head h_ne).1 + k ∧
      (vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords vertices)[k] ∧
      (∀ hidx_next : idx + 1 < vertices.length,
        (vertices.get ⟨idx + 1, hidx_next⟩).1 = (vertices.get ⟨idx, hidx⟩).1 + 1 ∧
        (vertices.get ⟨idx + 1, hidx_next⟩).2 = (vertices.get ⟨idx, hidx⟩).2) := by
  induction vertices generalizing k with
  | nil => simp [lgvPathEastStepYCoords] at hk
  | cons v₀ tl ih =>
    cases tl with
    | nil => simp [lgvPathEastStepYCoords] at hk
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords] at hk ⊢
      have h_arcs' : ∀ j : ℕ, ∀ hj : j + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨j, Nat.lt_of_succ_lt hj⟩)
            ((v₁ :: rest).get ⟨j + 1, hj⟩) := by
        intro j hj
        have hj' : (j + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hj ⊢; omega
        have := h_arcs (j + 1) hj'
        simp at this ⊢; exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil _ _
      have harc := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at harc
      simp only [LGV.integerLattice] at harc
      split_ifs at hk ⊢ with h_east
      · -- v₀ → v₁ is an east step
        obtain ⟨heast_x, heast_y⟩ := h_east
        cases k with
        | zero =>
          -- The 0th element is v₀.2, and x = start_x + 0 = v₀.1
          refine ⟨0, by simp, ?_, ?_, ?_⟩
          · simp [List.head_cons]
          · rfl
          · intro hidx_next
            simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
            exact ⟨heast_x, heast_y⟩
        | succ k' =>
          -- Use IH on the tail
          simp at hk
          have ih' := ih h_ne' h_arcs' k' hk
          obtain ⟨idx, hidx, hx, hy, heast_step⟩ := ih'
          simp only [List.get_eq_getElem, List.head_cons] at hx
          have hidx' : idx + 1 < (v₀ :: v₁ :: rest).length := by
            simp only [List.length_cons] at hidx ⊢; omega
          refine ⟨idx + 1, hidx', ?_, ?_, ?_⟩
          · simp only [List.get_eq_getElem, List.head_cons]
            have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
            rw [heq, hx]
            omega
          · simp only [List.get_eq_getElem] at hy ⊢
            have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
            rw [heq, hy]
            simp [List.getElem_cons_succ]
          · intro hidx_next
            have hidx_tail : idx + 1 < (v₁ :: rest).length := by simp at hidx_next hidx ⊢; omega
            have heast_tail := heast_step hidx_tail
            simp only [List.get_eq_getElem] at heast_tail ⊢
            constructor
            · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
              have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
              rw [h1, h2]; exact heast_tail.1
            · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
              have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
              rw [h1, h2]; exact heast_tail.2
      · -- v₀ → v₁ is a north step
        -- The list is just lgvPathEastStepYCoords (v₁ :: rest)
        -- Use IH
        have ih' := ih h_ne' h_arcs' k hk
        obtain ⟨idx, hidx, hx, hy, heast_step⟩ := ih'
        simp only [List.get_eq_getElem, List.head_cons] at hx
        have hidx' : idx + 1 < (v₀ :: v₁ :: rest).length := by
          simp only [List.length_cons] at hidx ⊢; omega
        refine ⟨idx + 1, hidx', ?_, ?_, ?_⟩
        · simp only [List.get_eq_getElem, List.head_cons]
          have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
          rw [heq, hx]
          -- v₁.1 = v₀.1 from north step
          rcases harc with ⟨hx', hy'⟩ | ⟨hx', _⟩
          · -- East step, but h_east says not
            simp at h_east
            have hne : v₁.2 ≠ v₀.2 := h_east hx'
            exact absurd hy' hne
          · omega
        · simp only [List.get_eq_getElem] at hy ⊢
          have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
          rw [heq, hy]
        · intro hidx_next
          have hidx_tail : idx + 1 < (v₁ :: rest).length := by simp at hidx_next hidx ⊢; omega
          have heast_tail := heast_step hidx_tail
          simp only [List.get_eq_getElem] at heast_tail ⊢
          constructor
          · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
            have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
            rw [h1, h2]; exact heast_tail.1
          · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
            have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
            rw [h1, h2]; exact heast_tail.2

/-- The k-th east-step y-coordinate equals the y-coordinate at x = start_x + k.

    This lemma establishes that `lgvPathEastStepYCoords[k]` is the y-coordinate of the
    path at x-coordinate start_x + k, where start_x is the x-coordinate of the first vertex.

    The k-th east step occurs at x = start_x + k because:
    - The path starts at x = start_x
    - Each east step increases x by 1
    - The k-th east step is preceded by exactly k east steps (indices 0, 1, ..., k-1)
    - So the k-th east step starts at x = start_x + k -/
theorem lgvPathEastStepYCoords_at_x (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords p.vertices).length) :
    ∃ (idx : ℕ) (hidx : idx < p.vertices.length),
      (p.vertices.get ⟨idx, hidx⟩).1 = p.start.1 + k ∧
      (p.vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords p.vertices)[k] := by
  have h := lgvPathEastStepYCoords_at_x_aux p.vertices p.nonempty p.arcs_valid k hk
  obtain ⟨idx, hidx, hx, hy, _⟩ := h
  refine ⟨idx, hidx, ?_, hy⟩
  simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem] at hx ⊢
  convert hx using 2

/-- The index returned by lgvPathEastStepYCoords_at_x is the start of an east step.
    If idx + 1 < vertices.length, then the step from idx to idx+1 is an east step. -/
theorem lgvPathEastStepYCoords_at_x_is_east_step (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords p.vertices).length)
    (idx : ℕ) (hidx : idx < p.vertices.length)
    (_hx : (p.vertices.get ⟨idx, hidx⟩).1 = p.start.1 + k)
    (hy : (p.vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords p.vertices)[k])
    (hidx_next : idx + 1 < p.vertices.length) :
    (p.vertices.get ⟨idx + 1, hidx_next⟩).1 = (p.vertices.get ⟨idx, hidx⟩).1 + 1 ∧
    (p.vertices.get ⟨idx + 1, hidx_next⟩).2 = (p.vertices.get ⟨idx, hidx⟩).2 := by
  -- Use the strengthened auxiliary lemma which proves this directly
  have h := lgvPathEastStepYCoords_at_x_aux p.vertices p.nonempty p.arcs_valid k hk
  obtain ⟨idx', hidx', hx', hy', heast_step⟩ := h

  -- The step from idx to idx+1 is either east or north
  have harc := p.arcs_valid idx hidx_next
  rcases harc with ⟨heast_x, heast_y⟩ | ⟨hnorth_x, hnorth_y⟩
  · -- East step: this is what we want to prove
    constructor
    · have h1 : (p.vertices.get ⟨idx, Nat.lt_of_succ_lt hidx_next⟩).1 =
                (p.vertices.get ⟨idx, hidx⟩).1 := rfl
      rw [← h1]; exact heast_x
    · have h1 : (p.vertices.get ⟨idx, Nat.lt_of_succ_lt hidx_next⟩).2 =
                (p.vertices.get ⟨idx, hidx⟩).2 := rfl
      rw [← h1]; exact heast_y
  · -- North step: contradiction
    -- We show idx = idx' using the fact that the path has no duplicate vertices
    -- (since integer lattice is acyclic)

    -- First, show that the vertices at idx and idx' are equal
    have hv_eq : p.vertices.get ⟨idx, hidx⟩ = p.vertices.get ⟨idx', hidx'⟩ := by
      ext
      · -- x-coordinates equal: both are start.x + k
        simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem] at _hx hx'
        have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
        have hx1 : (p.vertices.get ⟨idx, hidx⟩).1 = (p.vertices[0]'hlen).1 + k := _hx
        have hx2 : (p.vertices.get ⟨idx', hidx'⟩).1 = (p.vertices[0]'hlen).1 + k := by
          simp only [List.get_eq_getElem] at hx' ⊢
          convert hx' using 2
        omega
      · -- y-coordinates equal: both are ycoords[k]
        rw [hy, hy']

    -- The path has no duplicate vertices (since integer lattice is acyclic)
    have hnodup := LGV.SimpleDigraph.Path.vertices_nodup_of_acyclic LGV.integerLattice_acyclic p
    rw [List.nodup_iff_injective_getElem] at hnodup

    -- Since vertices at idx and idx' are equal, idx = idx'
    have hidx_eq : idx = idx' := by
      have hinj := @hnodup ⟨idx, hidx⟩ ⟨idx', hidx'⟩
      simp only [Fin.mk.injEq] at hinj
      simp only [List.get_eq_getElem] at hv_eq
      exact hinj hv_eq

    -- Now use the east step property from the aux lemma
    -- The east step property says: step from idx' to idx'+1 is east (x+1, y same)
    -- But hnorth_x says: step from idx to idx+1 has x unchanged
    -- Since idx = idx', this is a contradiction

    have hidx_next' : idx' + 1 < p.vertices.length := by rw [← hidx_eq]; exact hidx_next
    have heast := heast_step hidx_next'
    simp only [List.get_eq_getElem] at heast

    -- heast.1 says x(idx'+1) = x(idx') + 1
    -- hnorth_x says x(idx+1) = x(idx)
    -- Since idx = idx', we have x(idx'+1) = x(idx') and x(idx'+1) = x(idx') + 1
    -- This gives 0 = 1, contradiction

    have hx_east : p.vertices[idx' + 1].1 = p.vertices[idx'].1 + 1 := heast.1
    have hx_north : p.vertices[idx + 1].1 = p.vertices[idx].1 := by
      have := hnorth_x
      simp only [List.get_eq_getElem] at this
      exact this
    -- Substitute idx = idx' into hx_north
    subst hidx_eq
    -- Now hx_north : p.vertices[idx' + 1].1 = p.vertices[idx'].1
    -- And hx_east : p.vertices[idx' + 1].1 = p.vertices[idx'].1 + 1
    -- This gives: p.vertices[idx'].1 = p.vertices[idx'].1 + 1, contradiction
    omega

/-- Helper: x-coordinate is monotone (non-decreasing) along a path in the integer lattice.
    This follows from the fact that each step is either east (x+1) or north (x unchanged). -/
theorem integerLattice_path_x_monotone (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j) :
    (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 := by
  induction j with
  | zero => simp only [Nat.le_zero] at hij; subst hij; rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · rfl
    · have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
      have h1 := ih hk (Nat.lt_succ_iff.mp hik)
      have hstep := LGV.integerLattice_path_x_step p k hj
      rcases hstep with h | h <;> omega

/-- Helper: if x-coordinates differ strictly, then indices differ strictly.
    Contrapositive of x-monotonicity. -/
theorem integerLattice_path_x_lt_implies_idx_lt (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length)
    (hx : (p.vertices.get ⟨i, hi⟩).1 < (p.vertices.get ⟨j, hj⟩).1) : i < j := by
  by_contra h; push Not at h
  have := integerLattice_path_x_monotone p j i hj hi h; omega

/-- Helper: at a fixed x-coordinate, the y-coordinates of vertices form a contiguous range
    starting from the first vertex at that x. 
    
    If vertex i has x = x₀ and vertex j has x = x₀ with i < j, then for any y in 
    [y_i, y_j], there exists a vertex k with i ≤ k ≤ j having (x₀, y).
    
    This follows from the fact that y changes by 0 or 1 at each step, and x stays the same
    during north steps (y increases by 1). -/
theorem integerLattice_path_y_contiguous_at_x (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (x₀ : ℤ)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j)
    (hx_i : (p.vertices.get ⟨i, hi⟩).1 = x₀)
    (hx_j : (p.vertices.get ⟨j, hj⟩).1 = x₀)
    (y : ℤ) (hy_lo : (p.vertices.get ⟨i, hi⟩).2 ≤ y) (hy_hi : y ≤ (p.vertices.get ⟨j, hj⟩).2) :
    ∃ (k : ℕ) (hk : k < p.vertices.length), i ≤ k ∧ k ≤ j ∧ 
      (p.vertices.get ⟨k, hk⟩).1 = x₀ ∧ (p.vertices.get ⟨k, hk⟩).2 = y := by
  -- Use discrete IVT on y-coordinates
  -- The y-coordinate at index i is y_i, at index j is y_j, and y ∈ [y_i, y_j]
  -- Since y changes by 0 or 1 at each step, there exists k with y_k = y
  induction j generalizing y with
  | zero =>
    simp only [Nat.le_zero] at hij
    subst hij
    exact ⟨0, hi, le_refl 0, le_refl 0, hx_i, by omega⟩
  | succ j' ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hij'
    · -- i = j' + 1
      exact ⟨j' + 1, hj, le_refl _, le_refl _, hx_j, by omega⟩
    · -- i < j' + 1, so i ≤ j'
      have hj'_lt : j' < p.vertices.length := Nat.lt_of_succ_lt hj
      -- Check if x at j' equals x₀
      have hstep := LGV.integerLattice_path_x_step p j' hj
      rcases hstep with hnorth | heast
      · -- North step: x(j'+1) - x(j') = 0, so x(j'+1) = x(j')
        -- Also y(j'+1) = y(j') + 1 (north step increases y by 1)
        have hx_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := by
          have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 0 := hnorth
          have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := rfl
          omega
        have hx_j' : (p.vertices.get ⟨j', hj'_lt⟩).1 = x₀ := by
          rw [hx_j] at hx_j'_eq
          exact hx_j'_eq.symm
        -- Get y-coordinate relation
        have hy_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).2 = (p.vertices.get ⟨j', hj'_lt⟩).2 + 1 := by
          have harc := p.arcs_valid j' hj
          rcases harc with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · -- East step: x increases by 1, y stays same
            -- But we know x(j'+1) - x(j') = 0 from hnorth, contradiction
            have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 + 1 := hx
            have h2 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 0 := hnorth
            omega
          · -- North step: x stays same, y increases by 1
            have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).2 = (p.vertices.get ⟨j', hj'_lt⟩).2 := rfl
            omega
        -- If y = y(j'+1), we're done
        by_cases hy_eq_j : y = (p.vertices.get ⟨j' + 1, hj⟩).2
        · exact ⟨j' + 1, hj, Nat.le_of_lt hij', le_refl _, hx_j, hy_eq_j.symm⟩
        · -- y < y(j'+1), so y ≤ y(j') = y(j'+1) - 1
          have hy_le_j' : y ≤ (p.vertices.get ⟨j', hj'_lt⟩).2 := by
            rw [hy_j'_eq] at hy_hi
            have := ne_iff_lt_or_gt.mp hy_eq_j
            rcases this with h | h
            · omega
            · omega
          -- Apply IH to find vertex at index ≤ j' with y-coordinate y
          have := ih hj'_lt (Nat.lt_succ_iff.mp hij') hx_j' y hy_lo hy_le_j'
          obtain ⟨k, hk, hik, hkj', hx_k, hy_k⟩ := this
          exact ⟨k, hk, hik, Nat.le_succ_of_le hkj', hx_k, hy_k⟩
      · -- East step: x(j'+1) - x(j') = 1, so x(j'+1) = x(j') + 1
        -- Since x(j'+1) = x₀, we have x(j') = x₀ - 1 ≠ x₀
        have hx_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 + 1 := by
          have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 1 := heast
          have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := rfl
          omega
        have hx_j' : (p.vertices.get ⟨j', hj'_lt⟩).1 = x₀ - 1 := by
          rw [hx_j] at hx_j'_eq
          omega
        -- If i = j', then x(i) = x₀ but x(j') = x₀ - 1, contradiction
        have hi_ne_j' : i ≠ j' := by
          intro heq
          subst heq
          rw [hx_i] at hx_j'
          omega
        -- So i < j'
        have hi_lt_j' : i < j' := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hij') hi_ne_j'
        -- x is non-decreasing, so x(i) ≤ x(j')
        have hx_i_le : (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j', hj'_lt⟩).1 := 
          integerLattice_path_x_monotone p i j' hi hj'_lt (Nat.le_of_lt hi_lt_j')
        -- But x(i) = x₀ and x(j') = x₀ - 1 < x₀, contradiction
        rw [hx_i, hx_j'] at hx_i_le
        omega

/-- Key lemma: for two non-intersecting paths, if one is above the other at some x-coordinate,
    it stays above at all greater x-coordinates where both paths have vertices.

    This is the "paths don't cross" property for x-coordinates.
    The proof uses discrete IVT: if the y-difference ever becomes ≤ 0, there must be
    a point where it equals 0, meaning the paths share a vertex (contradiction). -/
theorem paths_above_at_x_stays_above (p p' : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hni : ∀ v, v ∈ p.vertices → v ∉ p'.vertices)
    (x₀ : ℤ) -- x-coordinate where p' is above p
    -- Both paths have vertices at x₀
    (hx₀_p : ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = x₀)
    (hx₀_p' : ∃ (idx : ℕ) (hidx : idx < p'.vertices.length), (p'.vertices.get ⟨idx, hidx⟩).1 = x₀)
    -- p' is strictly above p at x₀
    (h_above : ∀ (idx_p : ℕ) (hidx_p : idx_p < p.vertices.length)
               (idx_p' : ℕ) (hidx_p' : idx_p' < p'.vertices.length),
               (p.vertices.get ⟨idx_p, hidx_p⟩).1 = x₀ →
               (p'.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₀ →
               (p'.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p.vertices.get ⟨idx_p, hidx_p⟩).2)
    -- A greater x-coordinate x₁
    (x₁ : ℤ) (hx₁ : x₁ ≥ x₀)
    -- Both paths have vertices at x₁
    (hx₁_p : ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = x₁)
    (hx₁_p' : ∃ (idx : ℕ) (hidx : idx < p'.vertices.length), (p'.vertices.get ⟨idx, hidx⟩).1 = x₁) :
    ∀ (idx_p : ℕ) (hidx_p : idx_p < p.vertices.length)
      (idx_p' : ℕ) (hidx_p' : idx_p' < p'.vertices.length),
      (p.vertices.get ⟨idx_p, hidx_p⟩).1 = x₁ →
      (p'.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₁ →
      (p'.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p.vertices.get ⟨idx_p, hidx_p⟩).2 := by
  -- The proof uses discrete IVT on the y-difference.
  -- If p' drops to or below p at some x > x₀, there must be a crossing point.
  intro idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
  by_contra h_not_above
  push Not at h_not_above
  -- Get witnesses for x₀
  obtain ⟨idx₀_p, hidx₀_p, hx₀_p_eq⟩ := hx₀_p
  obtain ⟨idx₀_p', hidx₀_p', hx₀_p'_eq⟩ := hx₀_p'
  -- At x₀, p' is strictly above p
  have h_above_at_x₀ := h_above idx₀_p hidx₀_p idx₀_p' hidx₀_p' hx₀_p_eq hx₀_p'_eq
  -- Define y-coordinate at x for each path (using the unique vertex at that x)
  -- The key insight: at x₁, if y_p' ≤ y_p, then by discrete IVT on x-coordinates,
  -- there exists some x ∈ [x₀, x₁] where y_p' = y_p, meaning paths share a vertex.
  --
  -- Use the sum-based approach: at x₀, sum_p = x₀ + y_p, sum_p' = x₀ + y_p'
  -- Since y_p' > y_p at x₀, sum_p' > sum_p.
  -- At x₁, if y_p' ≤ y_p, then sum_p' ≤ sum_p.
  -- By discrete IVT on sums, there's a sum s where both paths have the same y.
  -- Since x + y = s for both, and y is the same, x is the same.
  -- So paths share a vertex, contradiction.
  let y_p_x₀ := (p.vertices.get ⟨idx₀_p, hidx₀_p⟩).2
  let y_p'_x₀ := (p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩).2
  let y_p_x₁ := (p.vertices.get ⟨idx_p, hidx_p⟩).2
  let y_p'_x₁ := (p'.vertices.get ⟨idx_p', hidx_p'⟩).2
  -- Sums at x₀ and x₁
  let s_p_x₀ := x₀ + y_p_x₀
  let s_p'_x₀ := x₀ + y_p'_x₀
  let s_p_x₁ := x₁ + y_p_x₁
  let s_p'_x₁ := x₁ + y_p'_x₁
  -- At x₀: s_p'_x₀ > s_p_x₀ (since y_p'_x₀ > y_p_x₀)
  have hs₀ : s_p'_x₀ > s_p_x₀ := by simp only [s_p'_x₀, s_p_x₀]; omega
  -- At x₁: s_p'_x₁ ≤ s_p_x₁ (since y_p'_x₁ ≤ y_p_x₁ and both have x = x₁)
  have hs₁ : s_p'_x₁ ≤ s_p_x₁ := by simp only [s_p'_x₁, s_p_x₁]; omega
  -- The sums at vertices are determined by their index
  have hsum_p_x₀ := LGV.integerLattice_path_vertex_sum p idx₀_p hidx₀_p
  have hsum_p'_x₀ := LGV.integerLattice_path_vertex_sum p' idx₀_p' hidx₀_p'
  have hsum_p_x₁ := LGV.integerLattice_path_vertex_sum p idx_p hidx_p
  have hsum_p'_x₁ := LGV.integerLattice_path_vertex_sum p' idx_p' hidx_p'
  -- Case split: x₁ = x₀ or x₁ > x₀
  rcases eq_or_lt_of_le hx₁ with hx_eq | hx_gt
  · -- Case x₁ = x₀: contradiction with h_above and h_not_above
    subst hx_eq
    have := h_above idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
    omega
  · -- Case x₁ > x₀: use discrete IVT
    -- Define the y-difference function on sum values
    let y_p_fn (s : ℤ) : ℤ :=
      let idx := (s - p.start.1 - p.start.2).toNat
      if h : idx < p.vertices.length then (p.vertices.get ⟨idx, h⟩).2 else 0
    let y_p'_fn (s : ℤ) : ℤ :=
      let idx := (s - p'.start.1 - p'.start.2).toNat
      if h : idx < p'.vertices.length then (p'.vertices.get ⟨idx, h⟩).2 else 0
    let diff (s : ℤ) : ℤ := y_p'_fn s - y_p_fn s
    -- The key constraint: idx₀_p' < idx_p' (since x strictly increases from x₀ to x₁)
    have hidx_p'_mono : idx₀_p' < idx_p' := by
      have := integerLattice_path_x_lt_implies_idx_lt p' idx₀_p' idx_p' hidx₀_p' hidx_p'
      simp only [hx₀_p'_eq, hx_p'] at this
      exact this hx_gt
    -- Similarly for p: idx₀_p < idx_p
    have hidx_p_mono : idx₀_p < idx_p := by
      have := integerLattice_path_x_lt_implies_idx_lt p idx₀_p idx_p hidx₀_p hidx_p
      simp only [hx₀_p_eq, hx_p] at this
      exact this hx_gt
    -- The sum range for p' from x₀ to x₁ is [s_p'_x₀, s_p'_x₁]
    -- Since s_p'_x₁ ≤ s_p_x₁ and s_p'_x₀ < s_p'_x₁, we have s_p'_x₀ ≤ s_p_x₁
    have hs_p'_x₀_lt_sp'x₁ : s_p'_x₀ < s_p'_x₁ := by
      simp only [s_p'_x₀, s_p'_x₁]; omega
    have hs_p'_x₀_le_spx₁ : s_p'_x₀ ≤ s_p_x₁ := le_trans (le_of_lt hs_p'_x₀_lt_sp'x₁) hs₁
    -- Index bounds for the overlapping sum range
    have hidx_p_sp'x₀ : (s_p'_x₀ - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₀, s_p_x₀, s_p_x₁] at hs₀ hs_p'_x₀_le_spx₁; omega
    have hidx_p'_sp'x₀ : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₀]; omega
    have hidx_p_sp'x₁ : (s_p'_x₁ - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₁, s_p_x₁] at hs₁; omega
    have hidx_p'_sp'x₁ : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₁]; omega
    -- At s_p'_x₀, the index in p' is idx₀_p'
    have heq_idx_p'_sp'x₀ : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat = idx₀_p' := by
      simp only [s_p'_x₀]; omega
    -- At s_p'_x₁, the index in p' is idx_p'
    have heq_idx_p'_sp'x₁ : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat = idx_p' := by
      simp only [s_p'_x₁]; omega
    -- At s_p'_x₀, the x-coordinate of p is ≥ x₀
    have hx_p_at_sp'x₀ : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 ≥ x₀ := by
      have hidx_ge : (s_p'_x₀ - p.start.1 - p.start.2).toNat ≥ idx₀_p := by
        simp only [s_p'_x₀, s_p_x₀] at hs₀; omega
      have := integerLattice_path_x_monotone p idx₀_p (s_p'_x₀ - p.start.1 - p.start.2).toNat
        hidx₀_p hidx_p_sp'x₀ hidx_ge
      omega
    -- At s_p'_x₀, y_p' > y_p (or they share a vertex, contradiction)
    have hdiff_sp'x₀ : diff s_p'_x₀ > 0 := by
      simp only [diff, y_p_fn, y_p'_fn, hidx_p_sp'x₀, hidx_p'_sp'x₀, dite_true]
      by_contra h_le
      push Not at h_le
      have hsum_p_at_sp'x₀ := LGV.integerLattice_path_vertex_sum p
        (s_p'_x₀ - p.start.1 - p.start.2).toNat hidx_p_sp'x₀
      have hy_p'_val : (p'.vertices.get ⟨(s_p'_x₀ - p'.start.1 - p'.start.2).toNat, hidx_p'_sp'x₀⟩).2 = y_p'_x₀ := by
        have : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat = idx₀_p' := heq_idx_p'_sp'x₀
        simp only [List.get_eq_getElem, y_p'_x₀, this]
      have heq_y : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = y_p'_x₀ := by
        simp only [hy_p'_val] at h_le
        have hsum : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 +
               (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = s_p'_x₀ := by
          simp only [s_p'_x₀] at hsum_p_at_sp'x₀ ⊢; omega
        omega
      have heq_x : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 = x₀ := by
        have hsum : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 +
               (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = s_p'_x₀ := by
          simp only [s_p'_x₀] at hsum_p_at_sp'x₀ ⊢; omega
        omega
      have hv_eq : p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩ =
                   p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩ := by
        apply Prod.ext
        · simp only [heq_x, hx₀_p'_eq]
        · simp only [heq_y]; rfl
      have hmem_p : p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩ ∈ p.vertices :=
        List.get_mem p.vertices ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩
      have hmem_p' : p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩ ∈ p'.vertices :=
        List.get_mem p'.vertices ⟨idx₀_p', hidx₀_p'⟩
      rw [hv_eq] at hmem_p
      exact hni _ hmem_p hmem_p'
    -- At s_p'_x₁, diff ≤ 0
    have hdiff_sp'x₁ : diff s_p'_x₁ ≤ 0 := by
      simp only [diff, y_p_fn, y_p'_fn, hidx_p_sp'x₁, hidx_p'_sp'x₁, dite_true]
      have hy_p'_val : (p'.vertices.get ⟨(s_p'_x₁ - p'.start.1 - p'.start.2).toNat, hidx_p'_sp'x₁⟩).2 = y_p'_x₁ := by
        have : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat = idx_p' := heq_idx_p'_sp'x₁
        simp only [List.get_eq_getElem, y_p'_x₁, this]
      have hsum_p_at_sp'x₁ := LGV.integerLattice_path_vertex_sum p
        (s_p'_x₁ - p.start.1 - p.start.2).toNat hidx_p_sp'x₁
      have hx_p_le : (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).1 ≤ x₁ := by
        have hidx_le : (s_p'_x₁ - p.start.1 - p.start.2).toNat ≤ idx_p := by
          simp only [s_p'_x₁, s_p_x₁] at hs₁; omega
        have := integerLattice_path_x_monotone p (s_p'_x₁ - p.start.1 - p.start.2).toNat idx_p
          hidx_p_sp'x₁ hidx_p hidx_le
        omega
      simp only [hy_p'_val]
      have hsum : (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).1 +
             (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).2 = s_p'_x₁ := by
        simp only [s_p'_x₁] at hsum_p_at_sp'x₁ ⊢; omega
      omega
    -- The difference function changes by at most 1 at each step
    have hdiff_step : ∀ s : ℤ, s_p'_x₀ ≤ s → s < s_p'_x₁ → |diff (s + 1) - diff s| ≤ 1 := by
      intro s hs_lo hs_hi
      simp only [diff, y_p_fn, y_p'_fn]
      have hs_p_lo : s ≥ p.start.1 + p.start.2 := by
        simp only [s_p'_x₀, s_p_x₀] at hs_lo hs₀; omega
      have hs_p_hi : s < p.finish.1 + p.finish.2 := by
        have hlen := LGV.integerLattice_path_length_eq p
        simp only [s_p'_x₁, s_p_x₁] at hs_hi hs₁; omega
      have hs_p'_lo : s ≥ p'.start.1 + p'.start.2 := by
        simp only [s_p'_x₀] at hs_lo; omega
      have hs_p'_hi : s < p'.finish.1 + p'.finish.2 := by
        have hlen := LGV.integerLattice_path_length_eq p'
        simp only [s_p'_x₁] at hs_hi; omega
      have hidx_p_s : (s - p.start.1 - p.start.2).toNat < p.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p; omega
      have hidx_p'_s : (s - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p'; omega
      have hidx_p_s1 : (s + 1 - p.start.1 - p.start.2).toNat < p.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p; omega
      have hidx_p'_s1 : (s + 1 - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p'; omega
      simp only [hidx_p_s, hidx_p'_s, hidx_p_s1, hidx_p'_s1, dite_true]
      have heq_idx_p : (s + 1 - p.start.1 - p.start.2).toNat = (s - p.start.1 - p.start.2).toNat + 1 := by omega
      have heq_idx_p' : (s + 1 - p'.start.1 - p'.start.2).toNat = (s - p'.start.1 - p'.start.2).toNat + 1 := by omega
      have hstep_p_idx : (s - p.start.1 - p.start.2).toNat + 1 < p.vertices.length := by omega
      have hstep_p'_idx : (s - p'.start.1 - p'.start.2).toNat + 1 < p'.vertices.length := by omega
      have harc_p := p.arcs_valid (s - p.start.1 - p.start.2).toNat hstep_p_idx
      have harc_p' := p'.arcs_valid (s - p'.start.1 - p'.start.2).toNat hstep_p'_idx
      rcases harc_p with ⟨_, hy_p⟩ | ⟨_, hy_p⟩ <;>
      rcases harc_p' with ⟨_, hy_p'⟩ | ⟨_, hy_p'⟩ <;>
      · simp only [heq_idx_p, heq_idx_p', abs_le]
        constructor <;> omega
    -- Apply discrete IVT
    obtain ⟨s_eq, hs_eq_lo, hs_eq_hi, hdiff_eq⟩ := LGV.discrete_ivt (le_of_lt hs_p'_x₀_lt_sp'x₁) diff
      hdiff_step (le_of_lt hdiff_sp'x₀) hdiff_sp'x₁
    -- At s_eq, both paths have the same y-coordinate
    have hidx_p_seq : (s_eq - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₀, s_p_x₀, s_p'_x₁, s_p_x₁] at hs_eq_lo hs_eq_hi hs₀ hs₁; omega
    have hidx_p'_seq : (s_eq - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₀, s_p'_x₁] at hs_eq_lo hs_eq_hi; omega
    simp only [diff, y_p_fn, y_p'_fn, hidx_p_seq, hidx_p'_seq, dite_true, sub_eq_zero] at hdiff_eq
    -- Both paths have the same sum value at s_eq
    have hsum_p_seq := LGV.integerLattice_path_vertex_sum p (s_eq - p.start.1 - p.start.2).toNat hidx_p_seq
    have hsum_p'_seq := LGV.integerLattice_path_vertex_sum p' (s_eq - p'.start.1 - p'.start.2).toNat hidx_p'_seq
    -- Since x + y = s_eq for both, and y_p = y_p', we have x_p = x_p'
    have hx_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).1 =
                 (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).1 := by omega
    have hy_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).2 =
                 (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).2 := by omega
    -- The vertices are equal
    have hv_eq : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ =
                 p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ :=
      Prod.ext hx_eq hy_eq
    -- This contradicts non-intersection
    have hmem_p : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ ∈ p.vertices :=
      List.get_mem p.vertices ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩
    have hmem_p' : p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ ∈ p'.vertices :=
      List.get_mem p'.vertices ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩
    rw [hv_eq] at hmem_p
    exact hni _ hmem_p hmem_p'

end SymmetricFunctions
