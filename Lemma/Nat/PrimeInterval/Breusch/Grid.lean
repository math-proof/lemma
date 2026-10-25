import Mathlib
import sympy.Basic
import Def.NumberTheory.PrimeInterval.Breusch.Grid
open MathlibExt.NumberTheory.BreuschWanted.Internal


namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[w9_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma w9_length
-- imply
  w9.length = 16 :=
-- proof
  rfl

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[w9_complete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma w9_complete
-- imply
  (w9.map Prod.fst).toFinset = Nat.divisors Q9 := by
-- proof
  decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[w9_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma w9_pos
-- imply
  ∀ p ∈ w9, 1 ≤ p.1 := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[w9_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma w9_dvd
-- imply
  ∀ p ∈ w9, p.1 ∣ Q9 := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[M9_block0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma M9_block0
-- imply
  ∀ k < 2700, G9 (0 + k) ≤ 3 := by
-- proof
decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[M9_block1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma M9_block1
-- imply
  ∀ k < 2700, G9 (2700 + k) ≤ 3 := by
-- proof
decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[M9_block2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma M9_block2
-- imply
  ∀ k < 2700, G9 (5400 + k) ≤ 3 := by
-- proof
decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[M9_block3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma M9_block3
-- imply
  ∀ k < 2700, G9 (8100 + k) ≤ 3 := by
-- proof
decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[M9_block4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma M9_block4
-- imply
  ∀ k < 2700, G9 (10800 + k) ≤ 3 := by
-- proof
decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[M9_block5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma M9_block5
-- imply
  ∀ k < 2700, G9 (13500 + k) ≤ 3 := by
-- proof
decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[M9_block6](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma M9_block6
-- imply
  ∀ k < 2700, G9 (16200 + k) ≤ 3 := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[M9_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma M9_le
  :
-- imply
  ∀ j < 18900, G9 j ≤ 3 := by
-- proof
  intro j hj
  have hsplit :
    j < 2700 ∨
      2700 ≤ j ∧ j < 5400 ∨
        5400 ≤ j ∧ j < 8100 ∨
          8100 ≤ j ∧ j < 10800 ∨
            10800 ≤ j ∧ j < 13500 ∨ 13500 ≤ j ∧ j < 16200 ∨
              16200 ≤ j := by
    omega
  obtain h | h | h | h | h | h | h := hsplit
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.zero_le j)
    exact M9_block0 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block1 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block2 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block3 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block4 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block5 k (by omega)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact M9_block6 k (by omega)

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin1_attained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin1_attained
  :
-- imply
  G9 279 ≥ 1 := by
-- proof
decide
set_option maxRecDepth 16384 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin1_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin1_core
  :
-- imply
  ∀ j < 279, 10 ≤ j → G9 j < 1 := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin1
  :
-- imply
  G9 279 ≥ 1 ∧ ∀ j, 10 ≤ j → j < 279 → G9 j < 1 :=
-- proof
  ⟨jmin1_attained, fun j h1 h2 => jmin1_core j h2 h1⟩

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin2_attained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin2_attained
  :
-- imply
  G9 657 ≥ 2 := by
-- proof
decide
set_option maxRecDepth 16384 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin2_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin2_core
  :
-- imply
  ∀ j < 657, 10 ≤ j → G9 j < 2 := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin2
  :
-- imply
  G9 657 ≥ 2 ∧ ∀ j, 10 ≤ j → j < 657 → G9 j < 2 :=
-- proof
  ⟨jmin2_attained, fun j h1 h2 => jmin2_core j h2 h1⟩

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin3_attained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin3_attained
  :
-- imply
  G9 963 ≥ 3 := by
-- proof
decide
set_option maxRecDepth 16384 in

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin3_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin3_core
  :
-- imply
  ∀ j < 963, 10 ≤ j → G9 j < 3 := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[jmin3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma jmin3
  :
-- imply
  G9 963 ≥ 3 ∧ ∀ j, 10 ≤ j → j < 963 → G9 j < 3 :=
-- proof
  ⟨jmin3_attained, fun j h1 h2 => jmin3_core j h2 h1⟩

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[w9_mu_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma w9_mu_sign
-- imply
  ∀ q ∈ w9, q.2 = 1 ∨ q.2 = -1 := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[w9_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma w9_nodup
-- imply
  w9.Nodup := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[map_sum_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean)
-/
@[path]
lemma map_sum_toFinset
  [AddCommMonoid M]
  {l : List (ℕ × ℤ)}
  {f : (ℕ × ℤ) → M}
-- given
  (hl : l.Nodup) :
-- imply
  (l.map f).sum = l.toFinset.sum f := by
-- proof
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, ih hl.2, List.toFinset_cons,
      Finset.sum_insert (by simpa using hl.1)]

end MathlibExt.NumberTheory.BreuschWanted.Internal


-- created on 2026-10-20
-- updated on 2026-10-23
