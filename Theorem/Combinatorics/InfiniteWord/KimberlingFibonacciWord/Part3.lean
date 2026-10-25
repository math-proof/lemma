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
import Def.Combinatorics.InfiniteWord.KimberlingFibonacciWord.Part3


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
