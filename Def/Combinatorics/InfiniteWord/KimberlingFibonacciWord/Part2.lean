/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KimberlingFibonacciWord.lean -/

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
public import Theorem.Combinatorics.InfiniteWord.KimberlingFibonacciWord

@[expose] public section

section

namespace MetaMathlibExt

def kL (N : ℕ) : List (List Bool) := (List.range N).flatMap kCodes

end MetaMathlibExt
end
