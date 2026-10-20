import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence
open MetaMathlibExt
open GeneralizedThueMorse


/--
[shiftWord_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma shiftWord_mem_eq
  {L : Nat}
  {t : Fin L}
  {w : List (Fin L)}
  {b : Fin L} :
-- imply
  b ∈ shiftWord t w ↔ ∃ a ∈ w, shiftLetter a t = b := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.shiftWord_mem t w b

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
[shiftLetter_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma shiftLetter_val_eq
  {L : Nat}
  {a t : Fin L} :
-- imply
  (shiftLetter a t).val = (a.val + t.val) % L := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.shiftLetter_val a t

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
[block_prefix_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma block_prefix_succ_eq
  {L k : Nat}
  {kappa : Fin (k - 1) → Nat → Fin L}
  {n : Nat}
-- given
  (hL : 1 < L)
  (hk : 1 < k) :
-- imply
  ∃ tail, block L k hL hk kappa (n + 1) = block L k hL hk kappa n ++ tail := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.block_prefix_succ L k hL hk kappa n

/--
[block_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma block_prefix_eq
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
  apply MetaMathlibExt.GeneralizedThueMorse.block_prefix L k hL hk kappa h

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

/--
[get_append_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma get_append_left_eq
  {l₁ l₂ : List α}
  {m : Nat}
-- given
  (h : m < (l₁ ++ l₂).length)
  (hm : m < l₁.length) :
-- imply
  (l₁ ++ l₂).get ⟨m, h⟩ = l₁.get ⟨m, hm⟩ := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.get_append_left l₁ l₂ m h hm

/--
[infLetter_coherence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma infLetter_coherence_eq
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
  apply MetaMathlibExt.GeneralizedThueMorse.infLetter_coherence L k hL hk kappa m N hN h

/--
[classical_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma classical_length_eq
  {n : Nat} :
-- imply
  (classicalBlock n).length = 2 ^ n := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.classical_length n

/--
[classical_A0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma classical_A0_eq
  :
-- imply
  classicalBlock 0 = [⟨0, by decide⟩] := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.classical_A0

/--
[classical_A1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma classical_A1_eq
  :
-- imply
  classicalBlock 1 = [⟨0, by decide⟩, ⟨1, by decide⟩] := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.classical_A1

/--
[classical_A2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma classical_A2_eq
  :
-- imply
  classicalBlock 2 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩] := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.classical_A2

/--
[classical_A3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma classical_A3_eq
  :
-- imply
  classicalBlock 3 =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩,
    ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] := by
-- proof
  apply MetaMathlibExt.GeneralizedThueMorse.classical_A3

/--
[classical_inf_init](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean)
-/
@[path]
private lemma classical_inf_init_eq
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
  apply MetaMathlibExt.GeneralizedThueMorse.classical_inf_init


-- created on 2026-10-20
