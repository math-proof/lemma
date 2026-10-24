/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean -/

import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Ring

/-!
# Generalized Thue-Morse sequence of type `(L, k, κ)`

Formalizes JIS Definition 2.2 and the classical `(2, 2, 1)` example immediately
following it (concept `jis_sem_12ac243c6e8826ae73e194e0`, source
`jis_source_8f34705c3f26ea83f401b8b0`, statements `jis_099e0392547ec836b0b913d1`
and `jis_6d78ade850f143086b5f8774`).
-/

namespace MetaMathlibExt

namespace GeneralizedThueMorse

/-- Cyclic letter shift for the `(L, k, κ)`-TM sequence
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statements
`jis_099e0392547ec836b0b913d1`/`jis_6d78ade850f143086b5f8774`):
sends `aᵢ` to `a_{i+t}` with the index taken modulo `L`. -/
def shiftLetter {L : Nat} (a t : Fin L) : Fin L :=
  ⟨(a.val + t.val) % L, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.2)⟩

/-- Letterwise action of a cyclic shift on words
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statements
`jis_099e0392547ec836b0b913d1`/`jis_6d78ade850f143086b5f8774`). -/
def shiftWord {L : Nat} (t : Fin L) (w : List (Fin L)) : List (Fin L) :=
  List.map (fun a => shiftLetter a t) w

/-- Shifting preserves word length
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem shiftWord_length {L : Nat} (t : Fin L) (w : List (Fin L)) :
    (shiftWord t w).length = w.length := by
  simp [shiftWord]

/-- Finite blocks `Aₙ` of the `(L, k, κ)`-TM sequence
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`):
`A₀` is the one-letter word `a₀`, and `Aₙ₊₁` concatenates `Aₙ` with each
whole-word cyclic shift `f^{κ(j,n)}(Aₙ)` for `j = 1, …, k-1`. -/
def block (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) : Nat → List (Fin L)
  | 0 => [⟨0, by omega⟩]
  | n + 1 =>
    let prev := block L k hL hk kappa n
    prev ++ List.flatten (List.map (fun j => shiftWord (kappa j n) prev) (List.finRange (k - 1)))

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

/-- The infinite word `A_∞`: its `m`-th letter is read from the finite block
`A_{m+1}`, proven long enough, via checked indexing with no default letter
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
def infLetter (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (m : Nat) : Fin L :=
  (block L k hL hk kappa (m + 1)).get
    ⟨m, by
      rw [block_length]
      exact lt_pow_succ_self hk m⟩

/-- Classical shift schedule `κ(1, n) = 1`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
def classicalKappa : Fin (2 - 1) → Nat → Fin 2 := fun _ _ => ⟨1, by decide⟩

/-- Classical blocks as a specialization of the general construction
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
def classicalBlock : Nat → List (Fin 2) :=
  block 2 2 (by decide) (by decide) classicalKappa
end GeneralizedThueMorse
end MetaMathlibExt
