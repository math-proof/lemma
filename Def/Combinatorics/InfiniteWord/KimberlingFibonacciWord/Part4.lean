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
public import Theorem.Combinatorics.InfiniteWord.KimberlingFibonacciWord.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KimberlingFibonacciWord.lean -/
section

namespace MetaMathlibExt

def kTail : ℕ → List Bool
  | 0 => [false, true]
  | 1 => [true, false]
  | (n + 2) => kTail n

def kConcat : ℕ → List Bool
  | 0 => []
  | (n + 1) => kConcat n ++ (fibWord n).reverse

end MetaMathlibExt
end
