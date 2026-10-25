import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.NumberTheory.Padics.Digits
open PadicInt Finset PadicIntTest


namespace PadicIntTest

/--
[appr_zero_test](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/Digits.lean)
-/
@[path]
lemma appr_zero_test
  {p : Nat}
  [Fact p.Prime]
  {n : Nat} :
-- imply
  PadicInt.appr (0 : ℤ_[p]) n = 0 := by
-- proof
  induction n with
  | zero => rfl
  | succ n ih => simp [PadicInt.appr, ih]

end PadicIntTest


-- created on 2026-10-23
