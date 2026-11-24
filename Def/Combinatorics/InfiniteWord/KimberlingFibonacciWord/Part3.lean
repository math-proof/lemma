module
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.InfiniteWord.FibonacciWord
public import Theorem.Finset.InfiniteWord.FibonacciWord
public import Theorem.Finset.Words.FibonacciFactorization
public import Theorem.Combinatorics.Words.FibonacciFactorization
public import Theorem.Combinatorics.InfiniteWord.KimberlingFibonacciWord.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KimberlingFibonacciWord.lean -/
section

namespace MetaMathlibExt

def kParLev (m : ℕ) : List Bool := (kCodes m).map fun w => decide (kVal w % 2 = 1)

end MetaMathlibExt
end
