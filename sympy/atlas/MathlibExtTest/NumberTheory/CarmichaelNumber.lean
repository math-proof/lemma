/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/CarmichaelNumber.lean -/


import sympy.atlas.NumberTheory.CarmichaelNumber
import Lemma.Nat.CarmichaelNumber
meta import Mathlib.Tactic.NormNum.Prime

example (x : ZMod 561) : x ^ 561 = x :=
  ((Nat.isCarmichaelNumber_iff_zmod 561).mp isCarmichaelNumber_561).2.2 x

example : ¬Nat.IsCarmichaelNumber 562 := by
  intro h
  have h562 : (1 : ℕ) < 562 := by norm_num
  have hk := (Nat.isCarmichaelNumber_iff_korselt 562 h562).mp h
  obtain ⟨_, hDiv, _⟩ := hk
  have h281Prime : Nat.Prime 281 := by norm_num
  have h281Dvd : 281 ∣ 562 := by norm_num
  have h280Dvd : (281 - 1) ∣ (562 - 1) := hDiv 281 h281Prime h281Dvd
  have hNot : ¬(280 ∣ 561) := by norm_num
  have hEq1 : (281 - 1 : ℕ) = 280 := by norm_num
  have hEq2 : (562 - 1 : ℕ) = 561 := by norm_num
  rw [hEq1, hEq2] at h280Dvd
  exact hNot h280Dvd
