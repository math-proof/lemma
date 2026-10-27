import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.LucasSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[lucasU_fibonacciLucasParams](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSequence.lean)
-/
@[path]
lemma lucasU_fibonacciLucasParams
  {n : ℕ} :
-- imply
  lucasU fibonacciLucasParams n = (Nat.fib n : ℤ) := by
-- proof
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    calc
      lucasU fibonacciLucasParams (n + 2) =
        lucasU fibonacciLucasParams (n + 1) + lucasU fibonacciLucasParams n := by
        simp [lucasU, fibonacciLucasParams]
      _ = (Nat.fib (n + 1) : ℤ) + (Nat.fib n : ℤ) := by rw [ih1, ih2]
      _ = (Nat.fib (n + 2) : ℤ) := by rw [Nat.fib_add_two, Nat.cast_add, add_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucasV_fibonacciLucasParams](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSequence.lean)
-/
@[path]
lemma lucasV_fibonacciLucasParams
  {n : ℕ} :
-- imply
  lucasV fibonacciLucasParams n = (lucasNumber n : ℤ) := by
-- proof
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    calc
      lucasV fibonacciLucasParams (n + 2) =
        lucasV fibonacciLucasParams (n + 1) + lucasV fibonacciLucasParams n := by
        simp [lucasV, fibonacciLucasParams]
      _ = (lucasNumber (n + 1) : ℤ) + (lucasNumber n : ℤ) := by rw [ih1, ih2]
      _ = (lucasNumber (n + 2) : ℤ) := by simp [lucasNumber]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
