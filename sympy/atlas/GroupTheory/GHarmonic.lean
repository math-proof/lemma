/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean -/

import Mathlib.GroupTheory.Index

open scoped Pointwise

/-! # G-harmonic tuples

Source: Murali Menon, "Two Questions on G-Harmonic Tuples"
(https://arxiv.org/abs/2608.15873v1, Definition span lines 33--37 of `main.tex`).
For a group `G`, a tuple `a : Fin n → ℕ` of positive integers is `G`-harmonic when
subgroups `U i` of exact index `a i` have left cosets `g i • (U i : Set G)` that
are pairwise disjoint. Since `Subgroup.index` is `0` for infinite index,
positivity plus exact index equality rules out infinite index. -/

/-- A tuple `a` is `G`-harmonic when each entry is positive and subgroups of
exactly those indices have pairwise disjoint left cosets. -/
def IsGHarmonic (G : Type*) [Group G] {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 0 < a i) ∧
    ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
      (∀ i, (U i).index = a i) ∧
        Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G))

/-- Constructor repackaging the definition. -/
theorem IsGHarmonic.intro {G : Type*} [Group G] {n : ℕ} {a : Fin n → ℕ}
    (hpos : ∀ i, 0 < a i) (U : Fin n → Subgroup G) (g : Fin n → G)
    (hidx : ∀ i, (U i).index = a i)
    (hdisj : Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G))) :
    IsGHarmonic G a :=
  ⟨hpos, U, g, hidx, hdisj⟩

/-- Each entry of a `G`-harmonic tuple is positive. -/
theorem IsGHarmonic.pos {G : Type*} [Group G] {n : ℕ} {a : Fin n → ℕ}
    (h : IsGHarmonic G a) (i : Fin n) : 0 < a i :=
  h.1 i

/-- The witnessing subgroups and coset representatives. -/
theorem IsGHarmonic.witnesses {G : Type*} [Group G] {n : ℕ} {a : Fin n → ℕ}
    (h : IsGHarmonic G a) :
    ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
      (∀ i, (U i).index = a i) ∧
        Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) :=
  h.2

/-- Unfolding equivalence for rewriting. -/
theorem isGHarmonic_iff {G : Type*} [Group G] {n : ℕ} (a : Fin n → ℕ) :
    IsGHarmonic G a ↔
      (∀ i, 0 < a i) ∧
        ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
          (∀ i, (U i).index = a i) ∧
            Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) :=
  Iff.rfl

/-- The empty tuple is vacuously `G`-harmonic. -/
theorem isGHarmonic_empty {G : Type*} [Group G] :
    IsGHarmonic G (n := 0) Fin.elim0 := by
  refine ⟨fun i => Fin.elim0 i, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, ?_⟩
  intro i _ j _ hij
  exact (hij (Subsingleton.elim i j)).elim

/-- The positive singleton `(1)` is `G`-harmonic via `⊤` and `1`. -/
theorem isGHarmonic_singleton_one {G : Type*} [Group G] :
    IsGHarmonic G (n := 1) (fun _ => 1) := by
  refine ⟨fun _ => Nat.zero_lt_one, fun _ => ⊤, fun _ => 1, fun i => ?_, ?_⟩
  · exact Subgroup.index_top
  · intro i _ j _ hij
    exact (hij (Subsingleton.elim i j)).elim

/-- A tuple containing a zero entry is never `G`-harmonic. -/
theorem not_isGHarmonic_of_zero {G : Type*} [Group G] {n : ℕ} {a : Fin n → ℕ}
    (i : Fin n) (h0 : a i = 0) : ¬ IsGHarmonic G a := by
  intro h
  have hp := h.pos i
  rw [h0] at hp
  exact Nat.lt_irrefl 0 hp
