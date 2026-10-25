/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part5
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagMarkedTripleEquivPowerset {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    ZagMarkedTriple e π ≃
      {s : Finset (Fin n) // s ∈ (zagCycleMinima e π).powersetCard 3} := by
  classical
  let toMarked : ZagMarkedTriple e π →
      {s : Finset (Fin n) // s ∈ (zagCycleMinima e π).powersetCard 3} := fun m =>
    ⟨m.toFinset, Finset.mem_powersetCard.mpr
      ⟨m.toFinset_subset, m.toFinset_card⟩⟩
  refine Equiv.ofBijective toMarked ?_
  constructor
  · intro m m' hmm'
    have hset : m.toFinset = m'.toFinset := congrArg Subtype.val hmm'
    have hfirst_le (x : Fin n) (hx : x ∈ m.toFinset) : m.first ≤ x := by
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact le_rfl
      · exact m.first_lt_middle.le
      · exact (m.first_lt_middle.trans m.middle_lt_third).le
    have hfirst_le' (x : Fin n) (hx : x ∈ m'.toFinset) : m'.first ≤ x := by
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact le_rfl
      · exact m'.first_lt_middle.le
      · exact (m'.first_lt_middle.trans m'.middle_lt_third).le
    have hfirst : m.first = m'.first := le_antisymm
      (hfirst_le m'.first (by rw [hset]; simp [ZagMarkedTriple.toFinset]))
      (hfirst_le' m.first (by rw [← hset]; simp [ZagMarkedTriple.toFinset]))
    have hmm_le : m.middle ≤ m'.middle := by
      have hm : m'.middle ∈ m.toFinset := by
        rw [hset]
        simp [ZagMarkedTriple.toFinset]
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm
      · exfalso
        apply m'.first_lt_middle.ne
        exact (hfirst.symm.trans hm.symm)
      · exact hm.symm.le
      · rw [hm]
        exact m.middle_lt_third.le
    have hmm_ge : m'.middle ≤ m.middle := by
      have hm : m.middle ∈ m'.toFinset := by
        rw [← hset]
        simp [ZagMarkedTriple.toFinset]
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm
      · exfalso
        apply m.first_lt_middle.ne
        exact hfirst.trans hm.symm
      · exact hm.symm.le
      · rw [hm]
        exact m'.middle_lt_third.le
    have hmiddle : m.middle = m'.middle := le_antisymm hmm_le hmm_ge
    have hthird : m.third = m'.third := by
      have hm : m.third ∈ m'.toFinset := by
        rw [← hset]
        simp [ZagMarkedTriple.toFinset]
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm
      · exfalso
        apply (m.first_lt_middle.trans m.middle_lt_third).ne
        exact hfirst.trans hm.symm
      · exfalso
        apply m.middle_lt_third.ne
        exact hmiddle.trans hm.symm
      · exact hm
    exact zagMarkedTriple_ext hfirst hmiddle hthird
  · intro s
    have hcard : s.1.card = 3 := (Finset.mem_powersetCard.mp s.2).2
    let o := s.1.orderIsoOfFin hcard
    let m : ZagMarkedTriple e π := {
      first := (o 0).1
      middle := (o 1).1
      third := (o 2).1
      first_mem := (Finset.mem_powersetCard.mp s.2).1 (o 0).2
      middle_mem := (Finset.mem_powersetCard.mp s.2).1 (o 1).2
      third_mem := (Finset.mem_powersetCard.mp s.2).1 (o 2).2
      first_lt_middle := by
        exact o.lt_iff_lt.mpr (by decide)
      middle_lt_third := by
        exact o.lt_iff_lt.mpr (by decide)
    }
    refine ⟨m, Subtype.ext ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      change x ∈ {m.first, m.middle, m.third} at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · rw [hx]
        change ↑(o 0) ∈ s.1
        exact (o 0).2
      · rw [hx]
        change ↑(o 1) ∈ s.1
        exact (o 1).2
      · rw [hx]
        change ↑(o 2) ∈ s.1
        exact (o 2).2
    · rw [ZagMarkedTriple.toFinset_card, hcard]

end MetaMathlibExt
