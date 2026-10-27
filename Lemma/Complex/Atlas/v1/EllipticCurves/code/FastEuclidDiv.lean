import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.FastEuclidDiv
open IntegerLongDivision


namespace IntegerLongDivision

/--
[testBit_toNat_eq_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FastEuclidDiv.lean)
-/
@[path]
lemma testBit_toNat_eq_mod_two
  {n k : ℕ} :
-- imply
  (n.testBit k).toNat = n / 2 ^ k % 2 := by
-- proof
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have h : n / 2 ^ k % 2 = 0 ∨ n / 2 ^ k % 2 = 1 := by omega
  obtain h | h <;> simp [h] := h

end IntegerLongDivision

namespace IntegerLongDivision

/--
[div_pow_two_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FastEuclidDiv.lean)
-/
@[path]
lemma div_pow_two_step
  {a k : ℕ} :
-- imply
  a / 2 ^ k = 2 * (a / 2 ^ (k + 1)) + (a.testBit k).toNat := by
-- proof
  rw [testBit_toNat_eq_mod_two]
  have : a / 2 ^ (k + 1) = a / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [this]; omega

end IntegerLongDivision

namespace IntegerLongDivision

/--
[longDivStep_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FastEuclidDiv.lean)
-/
@[path]
lemma longDivStep_invariant
  {b : ℕ}
  {bit : Bool}
  {q r : ℕ}
-- given
  (hr : r < b) :
-- imply
  let res := longDivStep b bit (q, r) res.1 * b + res.2 = 2 * (q * b + r) + bit.toNat ∧ res.2 < b := by
-- proof
  unfold longDivStep; simp only
  split_ifs with h
  · exact ⟨by ring, h⟩
  · push Not at h
    constructor
    · nlinarith [Nat.sub_add_cancel h]
    · have : bit.toNat ≤ 1 := by cases bit <;> simp
      omega

end IntegerLongDivision

namespace IntegerLongDivision

/--
[longDivLoop_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FastEuclidDiv.lean)
-/
@[path]
lemma longDivLoop_invariant
  {a b m : ℕ}
-- given
  (hb : 0 < b)
  (ham : a < 2 ^ (m + 1)) :
-- imply
  ∀ k, k ≤ m → let res :=
-- proof
  longDivLoop a b m k
    res.1 * b + res.2 = a / 2 ^ (m - k) ∧ res.2 < b := by
    intro k hk
    induction k with
    | zero =>
      simp only [longDivLoop, Nat.sub_zero]
      obtain ⟨heq, hr⟩ := longDivStep_invariant b (a.testBit m) 0 0 hb
      simp at heq
      refine ⟨?_, hr⟩
      rw [heq, div_pow_two_step a m, Nat.div_eq_of_lt ham]; ring
    | succ k ih =>
      simp only [longDivLoop]
      obtain ⟨heq, hr⟩ := ih (by omega : k ≤ m)
      obtain ⟨heq2, hr2⟩ := longDivStep_invariant b (a.testBit (m - k - 1)) _ _ hr
      refine ⟨?_, hr2⟩
      rw [heq2, heq]
      have hmk : m - (k + 1) = m - k - 1 := by omega
      rw [hmk, div_pow_two_step a (m - k - 1)]
      have : m - k - 1 + 1 = m - k := by omega
      rw [this]

end IntegerLongDivision

namespace IntegerLongDivision

/--
[long_division_correct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FastEuclidDiv.lean)
-/
@[path]
lemma long_division_correct
  {a b m : ℕ}
-- given
  (hb : 0 < b)
  (ham : a < 2 ^ (m + 1)) :
-- imply
  let res := longDiv a b m a = res.1 * b + res.2 ∧ res.2 < b := by
-- proof
  simp only [longDiv]
  obtain ⟨heq, hr⟩ := longDivLoop_invariant a b m hb ham m le_rfl
  simp only [Nat.sub_self, pow_zero, Nat.div_one] at heq
  exact ⟨heq.symm, hr⟩

end IntegerLongDivision


-- created on 2026-10-23
