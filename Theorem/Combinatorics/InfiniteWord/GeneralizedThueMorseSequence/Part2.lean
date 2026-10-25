/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean -/

import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Ring
import Def.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence.Part2
/-!
# Generalized Thue-Morse sequence of type `(L, k, κ)`

Formalizes JIS Definition 2.2 and the classical `(2, 2, 1)` example immediately
following it (concept `jis_sem_12ac243c6e8826ae73e194e0`, source
`jis_source_8f34705c3f26ea83f401b8b0`, statements `jis_099e0392547ec836b0b913d1`
and `jis_6d78ade850f143086b5f8774`).
-/


namespace MetaMathlibExt

namespace GeneralizedThueMorse

/-- Length of a flattened family of equal-length rows
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem length_flatten_eq {α : Type} (l : List (List α)) (m : Nat)
    (h : ∀ x ∈ l, x.length = m) : l.flatten.length = l.length * m := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x.length = m := h x (by simp)
    have hxs : ∀ y ∈ xs, y.length = m := fun y hy => h y (by simp [*])
    have hih := ih hxs
    have hflat : (List.flatten (x :: xs)).length = x.length + (List.flatten xs).length := by
      simp
    have hcons : (x :: xs).length = xs.length + 1 := by
      simp
    rw [hflat, hx, hih, hcons]
    ring

/-- Each block `Aₙ` has exactly `k^n` letters
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem block_length (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (n : Nat) :
    (block L k hL hk kappa n).length = k ^ n := by
  induction n with
  | zero => simp [block]
  | succ n ih =>
    have hmem : ∀ x ∈ List.map
        (fun j => shiftWord (kappa j n) (block L k hL hk kappa n))
        (List.finRange (k - 1)),
        x.length = (block L k hL hk kappa n).length := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      exact shiftWord_length _ _
    have hflen := length_flatten_eq _ _ hmem
    have hmap : (List.map
        (fun j => shiftWord (kappa j n) (block L k hL hk kappa n))
        (List.finRange (k - 1))).length = k - 1 := by
      simp
    have hunfold : block L k hL hk kappa (n + 1) =
        block L k hL hk kappa n ++
          List.flatten (List.map
            (fun j => shiftWord (kappa j n) (block L k hL hk kappa n))
            (List.finRange (k - 1))) :=
      rfl
    simp only [hunfold, List.length_append, ih, hflen, hmap, pow_succ]
    have e : k ^ n * k = k ^ n * ((k - 1) + 1) := by
      congr 1
      omega
    rw [e, mul_add, mul_one, Nat.mul_comm (k - 1) (k ^ n)]
    exact Nat.add_comm _ _

/-- Exponential lower bound used to select a long-enough block
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem lt_pow_succ_self {k : Nat} (hk : 1 < k) (m : Nat) : m < k ^ (m + 1) := by
  induction m with
  | zero => exact pow_pos (by omega) _
  | succ n ih =>
    have hpos : 0 < k ^ (n + 1) := pow_pos (by omega) _
    have hstep : k ^ (n + 1) < k ^ (n + 1) * k := lt_mul_of_one_lt_right hpos hk
    have hpow : k ^ ((n + 1) + 1) = k ^ (n + 1) * k := pow_succ k (n + 1)
    omega

end GeneralizedThueMorse
end MetaMathlibExt
