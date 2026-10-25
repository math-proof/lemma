/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KimberlingFibonacciWord.lean -/

import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.InfiniteWord.FibonacciWord
import Lemma.Finset.InfiniteWord.FibonacciWord
import Lemma.Finset.Words.FibonacciFactorization
import Theorem.Combinatorics.Words.FibonacciFactorization
import Theorem.Combinatorics.InfiniteWord.KimberlingFibonacciWord.Part3


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
