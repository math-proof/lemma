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

/-- The word shift acts letterwise
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem shiftWord_mem {L : Nat} (t : Fin L) (w : List (Fin L)) (b : Fin L) :
    b ∈ shiftWord t w ↔ ∃ a ∈ w, shiftLetter a t = b := by
  simp [shiftWord]

/-- Shifting preserves word length
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem shiftWord_length {L : Nat} (t : Fin L) (w : List (Fin L)) :
    (shiftWord t w).length = w.length := by
  simp [shiftWord]

/-- Value equation for the cyclic shift: it sends `aᵢ` to `a_{i+t mod L}`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem shiftLetter_val {L : Nat} (a t : Fin L) :
    (shiftLetter a t).val = (a.val + t.val) % L :=
  rfl

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

/-- Each block prefixes its successor
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem block_prefix_succ (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (n : Nat) :
    ∃ tail, block L k hL hk kappa (n + 1) = block L k hL hk kappa n ++ tail :=
  ⟨_, rfl⟩

/-- Blocks form a compatible chain of prefixes
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem block_prefix (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) {m n : Nat} (h : m ≤ n) :
    ∃ tail, block L k hL hk kappa n = block L k hL hk kappa m ++ tail := by
  induction n generalizing m with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact ⟨[], by simp⟩
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst hm
      exact ⟨[], by simp⟩
    · have hle : m ≤ n := by omega
      obtain ⟨tail, htail⟩ := ih hle
      obtain ⟨step, hstep⟩ := block_prefix_succ L k hL hk kappa n
      exact ⟨tail ++ step, by rw [hstep, htail, List.append_assoc]⟩

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

/-- Reading through an appended suffix agrees with reading the prefix
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
theorem get_append_left {α : Type} (l₁ l₂ : List α) (m : Nat)
    (h : m < (l₁ ++ l₂).length) (hm : m < l₁.length) :
    (l₁ ++ l₂).get ⟨m, h⟩ = l₁.get ⟨m, hm⟩ := by
  induction l₁ generalizing m with
  | nil => simp at hm
  | cons x xs ih =>
    cases m with
    | zero => rfl
    | succ m => exact ih m _ _

/-- The infinite word `A_∞`: its `m`-th letter is read from the finite block
`A_{m+1}`, proven long enough, via checked indexing with no default letter
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`). -/
def infLetter (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (m : Nat) : Fin L :=
  (block L k hL hk kappa (m + 1)).get
    ⟨m, by
      rw [block_length]
      exact lt_pow_succ_self hk m⟩

/-- Coherence of the limit: reading position `m` from any later block agrees
with `A_∞` (concept `jis_sem_12ac243c6e8826ae73e194e0`, statement
`jis_099e0392547ec836b0b913d1`). -/
theorem infLetter_coherence (L k : Nat) (hL : 1 < L) (hk : 1 < k)
    (kappa : Fin (k - 1) → Nat → Fin L) (m N : Nat) (hN : m + 1 ≤ N)
    (h : m < (block L k hL hk kappa N).length) :
    (block L k hL hk kappa N).get ⟨m, h⟩ = infLetter L k hL hk kappa m := by
  obtain ⟨tail, htail⟩ := block_prefix L k hL hk kappa hN
  have hm : m < (block L k hL hk kappa (m + 1)).length := by
    rw [block_length]
    exact lt_pow_succ_self hk m
  revert h
  rw [htail]
  intro h
  unfold infLetter
  exact get_append_left _ _ _ _ hm

/-- Classical shift schedule `κ(1, n) = 1`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
def classicalKappa : Fin (2 - 1) → Nat → Fin 2 := fun _ _ => ⟨1, by decide⟩

/-- Classical blocks as a specialization of the general construction
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
def classicalBlock : Nat → List (Fin 2) :=
  block 2 2 (by decide) (by decide) classicalKappa

/-- Classical length law
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
theorem classical_length (n : Nat) : (classicalBlock n).length = 2 ^ n := by
  exact block_length 2 2 _ _ _ n

/-- Classical block `A₀ = 0`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
theorem classical_A0 : classicalBlock 0 = [⟨0, by decide⟩] := by
  decide

/-- Classical block `A₁ = 01`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
theorem classical_A1 : classicalBlock 1 = [⟨0, by decide⟩, ⟨1, by decide⟩] := by
  decide

/-- Classical block `A₂ = 0110`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
theorem classical_A2 : classicalBlock 2 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩] := by
  decide

/-- Classical block `A₃ = 01101001`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
theorem classical_A3 : classicalBlock 3 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩,
     ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] := by
  decide

/-- The infinite classical word begins `01101001`
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_6d78ade850f143086b5f8774`). -/
theorem classical_inf_init :
    infLetter 2 2 (by decide) (by decide) classicalKappa 0 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 1 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 2 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 3 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 4 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 5 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 6 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 7 = ⟨1, by decide⟩ := by
  decide

end GeneralizedThueMorse

end MetaMathlibExt
