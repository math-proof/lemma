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
import Abbrev.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part9
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagOddVerticalDecompositionEquiv
    (n k : ℕ) (hn : 0 < n) (hparity : Even (n - k)) :
    ZagOddVerticalDecomposition n hn k ≃ ZagPlaneConfigDiagonal n hn k := by
  let toRaw : ZagOddVerticalDecomposition n hn k →
      ZagPlaneConfigDiagonal n hn k
    | Sum.inl q => q.1
    | Sum.inr q => q.2.1
  refine Equiv.ofBijective toRaw ?_
  constructor
  · intro a b hab
    rcases a with a | ⟨d, a⟩
    · rcases b with b | ⟨d, b⟩
      · apply congrArg Sum.inl
        apply Subtype.ext
        exact hab
      · have hcount := congrArg
          (fun q : ZagPlaneConfigDiagonal n hn k =>
            cycleQuotientCount q.1.2) hab
        rw [a.2, b.2] at hcount
        omega
    · rcases b with b | ⟨d', b⟩
      · have hcount := congrArg
          (fun q : ZagPlaneConfigDiagonal n hn k =>
            cycleQuotientCount q.1.2) hab
        rw [a.2, b.2] at hcount
        omega
      · have hcount := congrArg
          (fun q : ZagPlaneConfigDiagonal n hn k =>
            cycleQuotientCount q.1.2) hab
        rw [a.2, b.2] at hcount
        have hdd : d = d' := by
          apply Fin.ext
          omega
        subst d'
        apply congrArg Sum.inr
        apply Sigma.ext
        · rfl
        · exact heq_of_eq (Subtype.ext hab)
  · intro q
    let j := cycleQuotientCount q.1.2
    have hjOdd : Odd j :=
      zagVertical_cycleCount_odd hn hparity q.1.1.1 q.1.2 rfl q.2
    by_cases hjOne : j = 1
    · exact ⟨Sum.inl ⟨q, hjOne⟩, rfl⟩
    · obtain ⟨r, hr⟩ := hjOdd
      have hrpos : 0 < r := by
        by_contra hrzero
        have : r = 0 := by omega
        subst r
        simp only [mul_zero, zero_add] at hr
        exact hjOne hr
      have hjle : j ≤ n := by
        exact (show cycleQuotientCount q.1.2 ≤ n from
          zagCycleQuotientCount_le q.1.2)
      let d : Fin n := ⟨r - 1, by omega⟩
      have hjDepth : j = 2 * d.val + 3 := by
        dsimp only [d]
        omega
      exact ⟨Sum.inr ⟨d, ⟨q, hjDepth⟩⟩, rfl⟩

end MetaMathlibExt
