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
import Theorem.Combinatorics.InfiniteWord.KimberlingFibonacciWord.Part2


section

namespace MetaMathlibExt

def kParLev (m : ℕ) : List Bool := (kCodes m).map fun w => decide (kVal w % 2 = 1)

end MetaMathlibExt
end
