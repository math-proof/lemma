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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part29
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagOddMarksDepthEquivPowerset {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (d : ℕ) :
    {q : Σ root, ZagOddMarks e π root // q.2.depth = d} ≃
      {s : Finset (Fin n) //
        s ∈ (zagCycleMinima e π).powersetCard (2 * d + 3)} := by
  classical
  let toSubset :
      {q : Σ root, ZagOddMarks e π root // q.2.depth = d} →
        {s : Finset (Fin n) //
          s ∈ (zagCycleMinima e π).powersetCard (2 * d + 3)} := fun q =>
    ⟨q.1.2.toList.toFinset, Finset.mem_powersetCard.mpr ⟨by
      intro x hx
      exact q.1.2.mem_cycleMinima (by simpa using hx), by
      rw [List.toFinset_card_of_nodup q.1.2.nodup_toList,
        q.1.2.length_toList, q.2]⟩⟩
  refine Equiv.ofBijective toSubset ?_
  constructor
  · intro q q' hqq'
    apply Subtype.ext
    apply zagOddMarksSigma_ext
    apply q.1.2.sortedLT_toList.eq_of_mem_iff q'.1.2.sortedLT_toList
    intro x
    have hset := congrArg Subtype.val hqq'
    simpa only [toSubset, List.mem_toFinset] using Finset.ext_iff.mp hset x
  · intro s
    let l := s.1.sort
    have hsorted : l.SortedLT := s.1.sortedLT_sort
    have hmem : ∀ x ∈ l, x ∈ zagCycleMinima e π := by
      intro x hx
      exact (Finset.mem_powersetCard.mp s.2).1 (by simpa [l] using hx)
    have hlen : l.length = 2 * d + 3 := by
      change (s.1.sort).length = 2 * d + 3
      rw [Finset.length_sort]
      exact (Finset.mem_powersetCard.mp s.2).2
    have hodd : Odd l.length := by
      refine ⟨d + 1, ?_⟩
      omega
    have hthree : 3 ≤ l.length := by omega
    obtain ⟨root, m, hm⟩ :=
      zagOddMarks_exists_of_list e π l hsorted hmem hodd hthree
    have hdepth : m.depth = d := by
      have hmLength := m.length_toList
      rw [hm, hlen] at hmLength
      omega
    refine ⟨⟨⟨root, m⟩, hdepth⟩, Subtype.ext ?_⟩
    change m.toList.toFinset = s.1
    rw [hm]
    exact Finset.sort_toFinset s.1 (fun a b => a ≤ b)

end MetaMathlibExt
