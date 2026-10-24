/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimitiveDivisor.lean -/


import Mathlib.Data.Nat.Prime.Basic
import sympy.atlas.NumberTheory.PrimitiveDivisor
import Lemma.Nat.PrimitiveDivisor

namespace IntegerSequence

private def testSeq : ℕ → ℤ
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 6
  | _ => 0

example : IsPrimitivePrimeDivisor testSeq 2 2 := by
  refine ⟨Nat.prime_two, ⟨by decide, le_rfl, ?_, ?_⟩⟩
  · change (2 : ℤ) ∣ 2
    exact dvd_rfl
  · intro s hs hsm
    have : s = 1 := by omega
    subst this
    simp [testSeq]

example : IsPrimitivePrimeDivisor testSeq 3 3 := by
  refine ⟨Nat.prime_three, ⟨by omega, by omega, ?_, ?_⟩⟩
  · change (3 : ℤ) ∣ 3
    exact dvd_rfl
  · intro s hs hsm
    have : s = 1 ∨ s = 2 := by omega
    rcases this with rfl | rfl <;> simp [testSeq]

example : IsPrimitiveDivisor testSeq 4 6 := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · change (6 : ℤ) ∣ 6
    exact dvd_rfl
  · intro s hs hsm
    have : s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases this with rfl | rfl | rfl <;> simp [testSeq]

example : ¬ IsPrimitivePrimeDivisor testSeq 4 6 := by
  intro h
  exact (by decide : ¬Nat.Prime 6) h.prime

example : IsPrimitiveDivisor (fun _ => 2) 1 2 := by
  refine ⟨by decide, by decide, dvd_rfl, ?_⟩
  intro s hs hsm
  omega

example : ¬ IsPrimitiveDivisor testSeq 0 2 := by
  intro h
  exact (by omega : ¬1 ≤ 0) h.one_le

example : ¬ IsPrimitiveDivisor testSeq 2 1 := by
  intro h
  exact (by omega : ¬2 ≤ 1) h.two_le

example {a : ℕ → ℤ} {m u n : ℕ} (h : IsPrimitiveDivisor a m u)
    (hn : 1 ≤ n) (hd : (u : ℤ) ∣ a n) : m ≤ n :=
  h.le_of_dvd hn hd

example {a : ℕ → ℤ} {m n u : ℕ}
    (hm : IsPrimitiveDivisor a m u) (hn : IsPrimitiveDivisor a n u) : m = n :=
  hm.unique hn

end IntegerSequence
