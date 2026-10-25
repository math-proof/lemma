import Mathlib
import sympy.Basic
import Def.NumberTheory.PowerFree
open Nat


namespace Nat

/--
[isPowerFree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
lemma isPowerFree_iff
  {n k : ℕ} :
-- imply
  n.IsPowerFree k ↔ 2 ≤ k ∧ 0 < n ∧ ∀ p : ℕ, p.Prime → ¬p ^ k ∣ n :=
-- proof
  Iff.rfl

end Nat

namespace Nat

/--
[IsPowerFree.two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
lemma IsPowerFree.two_le
  {n k : ℕ}
-- given
  (h : n.IsPowerFree k) :
-- imply
  2 ≤ k :=
-- proof
  h.1

end Nat

namespace Nat

/--
[IsPowerFree.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
lemma IsPowerFree.pos
  {n k : ℕ}
-- given
  (h : n.IsPowerFree k) :
-- imply
  0 < n :=
-- proof
  h.2.1

end Nat

namespace Nat

/--
[IsPowerFree.not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
lemma IsPowerFree.not_dvd
  {n k p : ℕ}
-- given
  (h : n.IsPowerFree k)
  (hp : p.Prime) :
-- imply
  ¬p ^ k ∣ n :=
-- proof
  h.2.2 p hp

end Nat

namespace Nat

/--
[IsPowerFree.of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
lemma IsPowerFree.of_dvd
  {m n k : ℕ}
-- given
  (h : n.IsPowerFree k)
  (hmn : m ∣ n) :
-- imply
  m.IsPowerFree k :=
-- proof
  ⟨h.two_le, Nat.pos_of_dvd_of_pos hmn h.pos,
    fun _ hp hdiv => h.not_dvd hp (hdiv.trans hmn)⟩

end Nat

namespace Nat

/--
[IsPowerFree.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
lemma IsPowerFree.mono
  {n k l : ℕ}
-- given
  (h : n.IsPowerFree k)
  (hkl : k ≤ l) :
-- imply
  n.IsPowerFree l := by
-- proof
  refine ⟨le_trans h.two_le hkl, h.pos, fun p hp hdiv => ?_⟩
  have hpk : p ^ k ∣ p ^ l := by
    obtain ⟨d, rfl⟩ := Nat.le.dest hkl
    rw [pow_add]
    exact dvd_mul_right _ _
  exact h.not_dvd hp (hpk.trans hdiv)

end Nat

namespace Nat

/--
[isPowerFree_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
lemma isPowerFree_two
  {n : ℕ} :
-- imply
  n.IsPowerFree 2 ↔ Squarefree n := by
-- proof
  constructor
  · intro h
    rw [squarefree_iff_prime_squarefree]
    intro x hx hdiv
    exact h.not_dvd hx (by rwa [pow_two])
  · intro h
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [squarefree_iff_prime_squarefree] at h
      exact h 2 prime_two (dvd_zero _)
    refine ⟨le_refl 2, Nat.pos_of_ne_zero hn0, fun p hp hdiv => ?_⟩
    rw [squarefree_iff_prime_squarefree] at h
    exact h p hp (by rw [← pow_two]; exact hdiv)

end Nat


-- created on 2026-10-20
-- updated on 2026-10-23
