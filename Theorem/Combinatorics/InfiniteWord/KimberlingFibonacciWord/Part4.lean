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
import Def.Combinatorics.InfiniteWord.KimberlingFibonacciWord.Part4


section

namespace MetaMathlibExt

theorem kConcat_tail : ∀ n, kConcat n ++ kTail n = fibWord (n + 1)
  | 0 => by rfl
  | (n + 1) => by
    have ih := kConcat_tail n
    have eC : kConcat (n + 1) = kConcat n ++ (fibWord n).reverse := rfl
    rw [eC, List.append_assoc, ← kSwap n, ← List.append_assoc, ih]
    exact (fibWord_add_two n).symm

theorem kLPar_eq : ∀ N, ((kL N).map fun w => decide (kVal w % 2 = 1))
    = (List.range N).flatMap kParLev
  | 0 => by simp [kL]
  | N + 1 => by
    have ih := kLPar_eq N
    have eP : ((kCodes N).map fun w => decide (kVal w % 2 = 1)) = kParLev N := rfl
    have eS : List.flatMap kParLev [N] = kParLev N := by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [kL_succ, List.range_succ, List.map_append, List.flatMap_append, ih, eP, eS]

theorem kRangePar_eq : ∀ k,
    (List.range (k + 2)).flatMap kParLev = [true] ++ kConcat (k + 1)
  | 0 => by rfl
  | k + 1 => by
    change (List.range (k + 3)).flatMap kParLev = [true] ++ kConcat (k + 2)
    have ih := kRangePar_eq k
    have hr : List.range (k + 3) = List.range (k + 2) ++ [k + 2] := List.range_succ
    have eC : kConcat (k + 2) = kConcat (k + 1) ++ (fibWord (k + 1)).reverse := rfl
    have eR : kParLev (k + 2) = (fibWord (k + 1)).reverse := kParLev_eq (k + 1)
    have eS : List.flatMap kParLev [k + 2] = kParLev (k + 2) := by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hr, List.flatMap_append, ih, eS, eR, eC, List.append_assoc]

end MetaMathlibExt
end
