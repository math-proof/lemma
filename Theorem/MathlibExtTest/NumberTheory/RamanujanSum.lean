/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RamanujanSum.lean -/


import Def.NumberTheory.RamanujanSum
import Lemma.Nat.RamanujanSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open MetaMathlibExt

/-!
# Tests for Ramanujan sums
-/


example (n : ℕ) [NeZero n] : ramanujanSum n 0 = Nat.totient n := by
  simp

example (t : ℤ) : ramanujanSum 1 t = 1 := by
  simp

example : ramanujanSum 1 (-7) = 1 := by
  simp

example : ramanujanSum 2 1 = -1 := by
  have hcard : Fintype.card (ZMod 2)ˣ = 1 := by
    simp
  obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hcard
  let _ : Unique (ZMod 2)ˣ := { default := u, uniq := hu }
  rw [ramanujanSum, Fintype.sum_unique]
  change ZMod.stdAddChar (u.val * (1 : ZMod 2)) = -1
  have hu_one : u = 1 := (hu u).trans (hu 1).symm
  rw [hu_one, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  norm_num [ZMod.cast, ZMod.val_one]
  rw [show 2 * (Real.pi : ℂ) * Complex.I / 2 = (Real.pi : ℂ) * Complex.I by ring]
  exact Complex.exp_pi_mul_I

example (n : ℕ) [NeZero n] (t k : ℤ) :
    ramanujanSum n (t + k * n) = ramanujanSum n t := by
  simp

