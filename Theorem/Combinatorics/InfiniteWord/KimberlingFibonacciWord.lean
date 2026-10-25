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
import Def.Combinatorics.InfiniteWord.KimberlingFibonacciWord


section

namespace MetaMathlibExt

theorem kY_affine : ∀ (l : List Bool) (y : ℕ),
    l.foldl kYStep y = 2 ^ (kWeight l) * y + l.foldl kYStep 0
  | [], y => by simp [kWeight]
  | b :: u, y => by
    have h1 := kY_affine u (kYStep y b)
    have h0 := kY_affine u (kYStep 0 b)
    change u.foldl kYStep (kYStep y b) = 2 ^ (kWeight (b :: u)) * y + u.foldl kYStep (kYStep 0 b)
    rw [h1, h0]
    cases b
    case true =>
      have hy : kYStep y true = 4 * y + 1 := rfl
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hy, hz, hw, hp]
      ring
    case false =>
      have hy : kYStep y false = 2 * y + 1 := rfl
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hy, hz, hw, hp]
      ring

theorem kR_lt : ∀ (w : List Bool), w.foldl kYStep 0 < 2 ^ (kWeight w)
  | [] => by simp [kWeight]
  | b :: u => by
    have ih := kR_lt u
    have h1 := kY_affine u (kYStep 0 b)
    change u.foldl kYStep (kYStep 0 b) < 2 ^ (kWeight (b :: u))
    rw [h1]
    cases b
    case true =>
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hz, hw, hp]; omega
    case false =>
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hz, hw, hp]; omega

theorem kFold_ge_one : ∀ (l : List Bool) (s : ℕ), 1 ≤ s → 1 ≤ l.foldl kStep s
  | [], s, hs => hs
  | b :: u, s, hs => by
    change 1 ≤ u.foldl kStep (kStep s b)
    exact kFold_ge_one u _ (kStep_ge_one hs b)

theorem kFoldY_gen : ∀ (w : List Bool) (s : ℕ), 1 ≤ s →
    2 * (w.foldl kStep s) - 1 = 2 ^ (kWeight w) * (2 * s - 1) + w.foldl kYStep 0
  | [], s, _ => by simp [kWeight]
  | b :: u, s, hs => by
    have hs' : 1 ≤ kStep s b := kStep_ge_one hs b
    have h := kFoldY_gen u (kStep s b) hs'
    change 2 * (u.foldl kStep (kStep s b)) - 1
      = 2 ^ (kWeight (b :: u)) * (2 * s - 1) + u.foldl kYStep (kYStep 0 b)
    rw [h]
    have hR := kY_affine u (kYStep 0 b)
    rw [hR]
    cases b
    case true =>
      have e : kStep s true = 4 * s - 1 := rfl
      have hst : 2 * (kStep s true) - 1 = 4 * (2 * s - 1) + 1 := by omega
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hst, hz, hw, hp]
      ring
    case false =>
      have e : kStep s false = 2 * s := rfl
      have hst : 2 * (kStep s false) - 1 = 2 * (2 * s - 1) + 1 := by omega
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hst, hz, hw, hp]
      ring

end MetaMathlibExt
end
