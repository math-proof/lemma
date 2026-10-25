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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part3
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagCycleQuotientEquivMinima {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid π) ≃
      {i : Fin n // i ∈ zagCycleMinima e π} where
  toFun q := ⟨zagQuotientMinPos e π q, by
    rw [zag_mem_cycleMinima_iff]
    refine Quotient.inductionOn q ?_
    intro x
    change zagCycleMinPos e π (e (zagCycleMinPos e π x)) =
      zagCycleMinPos e π x
    exact zagCycleMinPos_eq_of_sameCycle e π
      (zagCycleMinPos_mem e π x)⟩
  invFun i := Quotient.mk _ (e i.1)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    exact zagCycleMinPos_mem e π x
  right_inv i := by
    apply Subtype.ext
    exact (zag_mem_cycleMinima_iff e π i.1).mp i.2

end MetaMathlibExt
