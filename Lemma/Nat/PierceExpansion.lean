import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.PierceExpansion.Part2
open PierceExpansion


namespace PierceExpansion

/--
[traj_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma traj_zero
  {n a : ℕ} :
-- imply
  traj n a 0 = a :=
-- proof
  rfl

end PierceExpansion

namespace PierceExpansion

/--
[traj_succ_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma traj_succ_of_eq_zero
  {n a j : ℕ}
-- given
  (h : traj n a j = 0) :
-- imply
  traj n a (j + 1) = 0 := by
-- proof
  simp only [traj, ite_eq_left h]

end PierceExpansion

namespace PierceExpansion

/--
[traj_succ_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma traj_succ_of_ne_zero
  {n a j : ℕ}
-- given
  (h : traj n a j ≠ 0) :
-- imply
  traj n a (j + 1) = n % traj n a j := by
-- proof
  simp only [traj, ite_eq_right h]

end PierceExpansion

namespace PierceExpansion

/--
[traj_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma traj_one
  {n t : ℕ}
-- given
  (ht : t ≠ 0) :
-- imply
  traj n t 1 = n % t := by
-- proof
  have h01 : (1 : ℕ) = 0 + 1 := rfl
  have h0 : traj n t 0 ≠ 0 := by
    rwa [traj_zero]
  rw [h01, traj_succ_of_ne_zero h0, traj_zero]

end PierceExpansion

namespace PierceExpansion

/--
[length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma length_pos
  {n a : ℕ} :
-- imply
  1 ≤ length n a :=
-- proof
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).1

end PierceExpansion

namespace PierceExpansion

/--
[traj_length_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma traj_length_eq_zero
  {n a : ℕ} :
-- imply
  traj n a (length n a) = 0 :=
-- proof
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).2

end PierceExpansion

namespace PierceExpansion

/--
[length_le_of_traj_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma length_le_of_traj_eq_zero
  {n a j : ℕ}
-- given
  (hj : 1 ≤ j)
  (h : traj n a j = 0) :
-- imply
  length n a ≤ j :=
-- proof
  Nat.find_min' _ ⟨hj, h⟩

end PierceExpansion

namespace PierceExpansion

/--
[traj_ne_zero_of_lt_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma traj_ne_zero_of_lt_length
  {n a j : ℕ}
-- given
  (hj : 1 ≤ j)
  (hlt : j < length n a) :
-- imply
  traj n a j ≠ 0 := by
-- proof
  have hneg := Nat.find_min _ hlt
  intro h0
  exact hneg ⟨hj, h0⟩

end PierceExpansion

namespace PierceExpansion

/--
[length_le_maxLength](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma length_le_maxLength
  {n a : ℕ}
-- given
  (ha : a ∈ Finset.Icc 1 n) :
-- imply
  length n a ≤ maxLength n :=
-- proof
  Finset.le_sup ha

end PierceExpansion

namespace PierceExpansion

/--
[maxLength_le_of_forall](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
lemma maxLength_le_of_forall
  {n L : ℕ}
-- given
  (h : ∀ a ∈ Finset.Icc 1 n, length n a ≤ L) :
-- imply
  maxLength n ≤ L :=
-- proof
  Finset.sup_le h

end PierceExpansion

/--
[exists_traj_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
private lemma exists_traj_eq_zero_eq
  {n a : ℕ} :
-- imply
  ∃ i ≤ a + 1, traj n a i = 0 := by
-- proof
  apply PierceExpansion.exists_traj_eq_zero n a

/--
[exists_traj_eq_zero_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean)
-/
@[path]
private lemma exists_traj_eq_zero_pos_eq
  {n a : ℕ} :
-- imply
  ∃ j ≥ 1, traj n a j = 0 := by
-- proof
  apply PierceExpansion.exists_traj_eq_zero_pos n a


-- created on 2026-10-20
-- updated on 2026-10-26
