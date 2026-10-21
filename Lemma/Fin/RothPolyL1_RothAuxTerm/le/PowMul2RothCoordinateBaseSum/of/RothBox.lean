import Mathlib
import Lemma.Fin.RothTermDegree.le.Sum.of.RothBox
import Lemma.Real.RothPolyL1_RothScaledPowerCoord.le.PowRothCoordinateBase.of.Le
open MathlibExt.NumberTheory.RothAuxiliary
open Fin Polynomial Real


/--
[rothAuxTerm_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (i j : RothBox r) :
-- imply
  rothPolyL1 (rothAuxTerm α i j) ≤
    (2 * rothCoordinateBase α) ^ (∑ h, r h) := by
-- proof
  let S := ∑ h, r h
  have hn : rothTermDegree i j ≤ S := RothTermDegree.le.Sum.of.RothBox i j
  have hch : (∏ h, Nat.choose (j h) (i h)) ≤ 2 ^ S := calc
    _ ≤ ∏ h, 2 ^ (j h : ℕ) := by
      gcongr with h
      exact Nat.choose_le_two_pow (j h) (i h)
    _ ≤ ∏ h, 2 ^ r h := by
      gcongr with h
      exact Nat.le_of_lt_succ (j h).isLt
    _ = 2 ^ S := Finset.prod_pow_eq_pow_sum Finset.univ r 2
  calc
    _ ≤ rothPolyL1 (C (∏ h, (Nat.choose (j h) (i h) : ℤ))) *
          rothPolyL1 (rothScaledPowerCoord α S (rothTermDegree i j)) :=
      RothPolyL1Mul.le.MulRothSPolyL1 _ _
    _ = (∏ h, Nat.choose (j h) (i h)) *
        rothPolyL1 (rothScaledPowerCoord α S (rothTermDegree i j)) := by
      rw [RothPolyL1_C.eq.NatAbs]
      change Int.natAbsHom (∏ h, (Nat.choose (j h) (i h) : ℤ)) * _ = _
      rw [map_prod]
      simp only [Int.natAbsHom_apply, Int.natAbs_natCast]
    _ ≤ 2 ^ S * rothCoordinateBase α ^ S :=
      Nat.mul_le_mul hch
        (RothPolyL1_RothScaledPowerCoord.le.PowRothCoordinateBase.of.Le α hn)
    _ = (2 * rothCoordinateBase α) ^ S := by rw [mul_pow]


-- created on 2026-10-21
