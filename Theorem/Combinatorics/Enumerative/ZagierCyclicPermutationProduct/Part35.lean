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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part33
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagReverseIndex_apply {n : ℕ} (hn : 0 < n) (i : Fin n) :
    zagReverseIndex n hn i = -i := by
  let hNeZero : NeZero n := ⟨hn.ne'⟩
  rfl

theorem zagReverseIndex_inv {n : ℕ} (hn : 0 < n) :
    (zagReverseIndex n hn)⁻¹ = zagReverseIndex n hn := by
  let hNeZero : NeZero n := ⟨hn.ne'⟩
  rfl

theorem zagReverseIndex_conj_finRotate {n : ℕ} (hn : 0 < n) :
    zagReverseIndex n hn * finRotate n * (zagReverseIndex n hn)⁻¹ =
      (finRotate n)⁻¹ := by
  let hNeZero : NeZero n := ⟨hn.ne'⟩
  apply Equiv.ext
  intro i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, zagReverseIndex_inv,
    zagReverseIndex_apply, zagReverseIndex_apply,
    finRotate_apply]
  change -(-i + 1) = (finRotate n).symm i
  rw [finRotate_symm_apply]
  simp only [neg_add_rev, neg_neg]
  exact (add_comm (-1 : Fin n) i).trans (sub_eq_add_neg i 1).symm

end MetaMathlibExt
