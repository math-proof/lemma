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
public import Def.Combinatorics.InfiniteWord.KimberlingFibonacciWord.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KimberlingFibonacciWord.lean -/
section

namespace MetaMathlibExt

theorem kMorph_conj : ∀ (s : List Bool),
    fibMorph s ++ [false] = [false] ++ (fibMorph s.reverse).reverse
  | [] => by rfl
  | b :: t => by
    have ih := kMorph_conj t
    cases b with
    | true =>
      have h1 : fibMorph (true :: t) = [false] ++ fibMorph t := rfl
      have eK : fibMorph [true] = [false] := rfl
      have eR : ([false] : List Bool).reverse = [false] := rfl
      rw [h1, List.reverse_cons, fibMorph_append, List.reverse_append, eK, eR]
      exact congrArg ([false] ++ ·) ih
    | false =>
      have h1 : fibMorph (false :: t) = [false, true] ++ fibMorph t := rfl
      have eK : fibMorph [false] = [false, true] := rfl
      have eR : ([false, true] : List Bool).reverse = [true, false] := rfl
      rw [h1, List.reverse_cons, fibMorph_append, List.reverse_append, eK, eR]
      exact congrArg ([false, true] ++ ·) ih

end MetaMathlibExt
end
