/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Recurrences/SkolemMahlerLech.lean -/


import Lemma.Nat.Recurrences.SkolemMahlerLech
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Bounded

-- A Fibonacci-type rational recurrence has a structured zero set.
example (u : ℕ → ℚ) (hrec : ∀ n, u (n + 2) = u n + u (n + 1)) :
    ∃ (F : Finset ℕ) (P : Finset (ℕ × ℕ)), (∀ p ∈ P, 0 < p.2) ∧
      {n | u n = 0} = ↑F ∪ ⋃ p ∈ (↑P : Set (ℕ × ℕ)), {n | ∃ t, n = p.1 + p.2 * t} := by
  apply MetaMathlibExt.skolemMahlerLech 2 (fun _ => 1) u
  intro n
  simpa [Finset.sum_range_succ] using hrec n

-- An infinite zero set contains a full infinite arithmetic progression.
example {K : Type*} [Field K] [CharZero K] (k : ℕ) (c u : ℕ → K)
    (hrec : ∀ n, u (n + k) = ∑ i ∈ Finset.range k, c i * u (n + i))
    (hinfinite : Set.Infinite {n | u n = 0}) :
    ∃ a d : ℕ, 0 < d ∧ ∀ t, u (a + d * t) = 0 := by
  obtain ⟨F, P, hpos, hzero⟩ := MetaMathlibExt.skolemMahlerLech k c u hrec
  have hP : P.Nonempty := by
    by_contra hP
    apply hinfinite
    rw [hzero, Finset.not_nonempty_iff_eq_empty.mp hP]
    simp
  obtain ⟨p, hp⟩ := hP
  refine ⟨p.1, p.2, hpos p hp, fun t => ?_⟩
  have hmem : p.1 + p.2 * t ∈ {n | u n = 0} := by
    rw [hzero]
    exact Set.mem_union_right _
      (Set.mem_biUnion (Finset.mem_coe.mpr hp) ⟨t, rfl⟩)
  exact hmem
