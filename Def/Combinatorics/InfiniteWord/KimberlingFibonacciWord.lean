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

@[expose] public section

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
