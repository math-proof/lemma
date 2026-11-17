module

public import Mathlib

public section


/--
[roth_pow_le_rpow_of_le_twice](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Real.Pow.le.RpowMul.of.LeSquare_Rpow.Le_Mul2.Ge_0.Ge_1
  (B q δ : ℝ)
  (S r : ℕ)
-- given
  (hB : 1 ≤ B)
  (hq : 0 ≤ q)
  (hS : S ≤ 2 * r)
  (hbase : B ^ 2 ≤ Real.rpow q δ) :
-- imply
  B ^ S ≤ Real.rpow q (δ * r) :=
-- proof
  calc
    _ ≤ B ^ (2 * r) := pow_le_pow_right₀ hB hS
    _ = (B ^ 2) ^ r := by rw [pow_mul]
    _ ≤ (Real.rpow q δ) ^ r := by gcongr
    _ = Real.rpow (Real.rpow q δ) (r : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = Real.rpow q (δ * (r : ℝ)) := (Real.rpow_mul hq _ _).symm


-- created on 2026-10-21
