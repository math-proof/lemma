/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Stormer.lean -/

module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Pell
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Squarefree

@[expose] public section

namespace MetaMathlibExt

section

def stormU (a : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 2 * a * stormU a (n + 1) - stormU a n

end
end MetaMathlibExt
