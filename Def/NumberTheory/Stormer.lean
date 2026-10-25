/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Stormer.lean -/

import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Squarefree


namespace MetaMathlibExt

section

def stormU (a : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 2 * a * stormU a (n + 1) - stormU a n

end
end MetaMathlibExt
