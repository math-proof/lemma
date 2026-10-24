/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean -/

import Mathlib.Data.List.Basic
import sympy.atlas.Combinatorics.InfiniteWord.FibonacciWord
import Lemma.Finset.InfiniteWord.FibonacciWord
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses

namespace MetaMathlibExt

private lemma fibWord_bridge (F : ℕ → List (Fin 2))
    (h_one : F 1 = [1]) (h_two : F 2 = [0])
    (h_rec : ∀ n : ℕ, F (n + 3) = F (n + 2) ++ F (n + 1)) :
    ∀ n : ℕ, F (n + 2) = (fibWord n).map (fun b => cond b 1 0)
  | 0 => by simp [h_two, fibWord]
  | 1 => by rw [h_rec 0, h_two, h_one]; rfl
  | n + 2 => by
    rw [show n + 2 + 2 = (n + 1) + 3 by omega, h_rec (n + 1),
      fibWord_bridge F h_one h_two h_rec (n + 1), show n + 1 + 1 = n + 2 by omega,
      fibWord_bridge F h_one h_two h_rec n, fibWord_add_two, List.map_append]

private lemma fibWord_concat_eq (F : ℕ → List (Fin 2))
    (h_one : F 1 = [1]) (h_two : F 2 = [0])
    (h_rec : ∀ n : ℕ, F (n + 3) = F (n + 2) ++ F (n + 1)) :
    ∀ N : ℕ, (0 :: (List.range N).flatMap (fun n => F (n + 1))) = F (N + 2)
  | 0 => by simp [h_two]
  | N + 1 => by
    have hb : ∀ n : ℕ, F (n + 1 + 1) = (fibWord n).map (fun b => cond b 1 0) :=
      fibWord_bridge F h_one h_two h_rec
    rw [fibWord_bridge F h_one h_two h_rec (N + 1), ← fibWord_factorization,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp [hb, h_one, List.map_flatMap]
end MetaMathlibExt
