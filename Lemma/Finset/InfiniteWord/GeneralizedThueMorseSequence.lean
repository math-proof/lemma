import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence
open MetaMathlibExt
open GeneralizedThueMorse


namespace MetaMathlibExt.GeneralizedThueMorse

/--
[shiftWord_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma shiftWord_mem
  {L : Nat}
  {t : Fin L}
  {w : List (Fin L)}
  {b : Fin L} :
-- imply
  b ∈ shiftWord t w ↔ ∃ a ∈ w, shiftLetter a t = b := by
-- proof
  simp [shiftWord]

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[shiftLetter_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma shiftLetter_val
  {L : Nat}
  {a t : Fin L} :
-- imply
  (shiftLetter a t).val = (a.val + t.val) % L :=
-- proof
  rfl

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[block_prefix_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma block_prefix_succ
  {L k : Nat}
  {kappa : Fin (k - 1) → Nat → Fin L}
  {n : Nat}
-- given
  (hL : 1 < L)
  (hk : 1 < k) :
-- imply
  ∃ tail, block L k hL hk kappa (n + 1) = block L k hL hk kappa n ++ tail :=
-- proof
  ⟨_, rfl⟩

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[block_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma block_prefix
  {L k : Nat}
  {kappa : Fin (k - 1) → Nat → Fin L}
  {m n : Nat}
-- given
  (hL : 1 < L)
  (hk : 1 < k)
  (h : m ≤ n) :
-- imply
  ∃ tail, block L k hL hk kappa n = block L k hL hk kappa m ++ tail := by
-- proof
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

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[get_append_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma get_append_left
  {l₁ l₂ : List α}
  {m : Nat}
-- given
  (h : m < (l₁ ++ l₂).length)
  (hm : m < l₁.length) :
-- imply
  (l₁ ++ l₂).get ⟨m, h⟩ = l₁.get ⟨m, hm⟩ := by
-- proof
  induction l₁ generalizing m with
  | nil => simp at hm
  | cons x xs ih =>
    cases m with
    | zero => rfl
    | succ m => exact ih m _ _

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[infLetter_coherence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma infLetter_coherence
  {L k : Nat}
  {kappa : Fin (k - 1) → Nat → Fin L}
  {m N : Nat}
-- given
  (hL : 1 < L)
  (hk : 1 < k)
  (hN : m + 1 ≤ N)
  (h : m < (block L k hL hk kappa N).length) :
-- imply
  (block L k hL hk kappa N).get ⟨m, h⟩ = infLetter L k hL hk kappa m := by
-- proof
  obtain ⟨tail, htail⟩ := block_prefix L k hL hk kappa hN
  have hm : m < (block L k hL hk kappa (m + 1)).length := by
    rw [block_length]
    exact lt_pow_succ_self hk m
  revert h
  rw [htail]
  intro h
  unfold infLetter
  exact get_append_left _ _ _ _ hm

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[classical_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma classical_length
  {n : Nat} :
-- imply
  (classicalBlock n).length = 2 ^ n :=
-- proof
block_length 2 2 _ _ _ n

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[classical_A0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma classical_A0
  :
-- imply
  classicalBlock 0 = [⟨0, by decide⟩] := by
-- proof
  decide

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[classical_A1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma classical_A1
  :
-- imply
  classicalBlock 1 = [⟨0, by decide⟩, ⟨1, by decide⟩] := by
-- proof
  decide

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[classical_A2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma classical_A2
  :
-- imply
  classicalBlock 2 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩] := by
-- proof
  decide

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[classical_A3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma classical_A3
  :
-- imply
  classicalBlock 3 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩,
    ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] := by
-- proof
  decide

end MetaMathlibExt.GeneralizedThueMorse

namespace MetaMathlibExt.GeneralizedThueMorse

/--
[classical_inf_init](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
lemma classical_inf_init
  :
-- imply
  infLetter 2 2 (by decide) (by decide) classicalKappa 0 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 1 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 2 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 3 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 4 = ⟨1, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 5 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 6 = ⟨0, by decide⟩ ∧
    infLetter 2 2 (by decide) (by decide) classicalKappa 7 = ⟨1, by decide⟩ := by
-- proof
  decide

end MetaMathlibExt.GeneralizedThueMorse

/--
[shiftWord_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma shiftWord_length_eq
  {L : Nat}
  {t : Fin L}
  {w : List (Fin L)} :
-- imply
  (shiftWord t w).length = w.length := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.shiftWord_length t w

/--
[length_flatten_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma length_flatten_eq_eq
  {l : List (List α)}
  {m : Nat}
-- given
  (h : ∀ x ∈ l, x.length = m) :
-- imply
  l.flatten.length = l.length * m := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.length_flatten_eq l m h

/--
[block_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma block_length_eq
  {L k : Nat}
  {kappa : Fin (k - 1) → Nat → Fin L}
  {n : Nat}
-- given
  (hL : 1 < L)
  (hk : 1 < k) :
-- imply
  (block L k hL hk kappa n).length = k ^ n := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.block_length L k hL hk kappa n

/--
[lt_pow_succ_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma lt_pow_succ_self_eq
  {k m : Nat}
-- given
  (hk : 1 < k) :
-- imply
  m < k ^ (m + 1) := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.lt_pow_succ_self hk m


-- created on 2026-10-20
-- updated on 2026-10-23
