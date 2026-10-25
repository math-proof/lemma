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


section

namespace MetaMathlibExt

/-! # Fibonacci word as self-generating set modulo 2
-/

def kYStep : ℕ → Bool → ℕ := fun y b => bif b then 4 * y + 1 else 2 * y + 1

def kWeight : List Bool → ℕ
  | [] => 0
  | b :: t => (bif b then 2 else 1) + kWeight t

def kStep : ℕ → Bool → ℕ := fun x b => bif b then 4 * x - 1 else 2 * x

def kVal : List Bool → ℕ := fun w => w.foldl kStep 1

def kCodes : ℕ → List (List Bool)
  | 0 => [[]]
  | 1 => [[false]]
  | (n + 2) => (kCodes n).map (List.cons true) ++ (kCodes (n + 1)).map (List.cons false)

end MetaMathlibExt
end
