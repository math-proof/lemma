/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeSupport.lean -/


import sympy.atlas.NumberTheory.PrimeSupport
import Lemma.Nat.PrimeSupport
import Mathlib.Tactic.NormNum


example (n : ℕ) : Nat.SamePrimeSupport n n :=
  Nat.samePrimeSupport_refl n

example {a b c : ℕ} (hab : Nat.SamePrimeSupport a b)
    (hbc : Nat.SamePrimeSupport b c) : Nat.SamePrimeSupport c a :=
  (hab.trans hbc).symm

example : ¬ Nat.SamePrimeSupport 0 1 := by
  intro h
  have h2 : 2 ∣ 1 := (h 2 Nat.prime_two).mp (dvd_zero 2)
  norm_num at h2

example : Nat.SamePrimeSupport 12 18 := by
  intro p hp
  change (p ∣ 2 * 2 * 3) ↔ (p ∣ 2 * 3 * 3)
  simp only [hp.dvd_mul]
  tauto
