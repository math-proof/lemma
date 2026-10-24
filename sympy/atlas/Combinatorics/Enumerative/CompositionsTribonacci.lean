/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.BigOperators
import sympy.atlas.NumberTheory.TribonacciSequenceWithInitialValues001
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compositions with parts one, two, and three

This file proves that compositions whose parts lie in `{1, 2, 3}` are counted by the
Tribonacci recurrence.
-/

namespace MetaMathlibExt

private def compositionsTrib_fixed (k n : ℕ) : ℕ :=
  Fintype.card {a : Fin k → Fin 3 // (∑ i : Fin k, ((a i).val + 1)) = n}

private def compositionsTrib_count (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), compositionsTrib_fixed k n

private def compositionsTrib_consEquiv (k n : ℕ) :
    {a : Fin (k + 1) → Fin 3 // (∑ i : Fin (k + 1), ((a i).val + 1)) = n} ≃
      Σ j : Fin 3, {b : Fin k → Fin 3 //
        (∑ i : Fin k, ((b i).val + 1)) + (j.val + 1) = n} where
  toFun a :=
    ⟨a.1 0, Fin.tail a.1, by
      have ha := a.2
      rw [Fin.sum_univ_succ] at ha
      simpa [Fin.tail, Nat.add_comm] using ha⟩
  invFun a :=
    ⟨Fin.cons a.1 a.2.1, by
      simpa [Fin.sum_univ_succ, Nat.add_comm] using a.2.2⟩
  left_inv a := by
    apply Subtype.ext
    exact Fin.cons_self_tail a.1
  right_inv a := by
    rcases a with ⟨j, b, hb⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    exact Fin.tail_cons (α := fun _ : Fin (k + 1) ↦ Fin 3) j b
end MetaMathlibExt
