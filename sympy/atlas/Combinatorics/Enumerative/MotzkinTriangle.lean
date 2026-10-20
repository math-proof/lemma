/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/

namespace MetaMathlibExt

/-- The discriminant `1 - 2X - 3X²` in the generating functions for the Motzkin triangle. -/
noncomputable def motzkinDiscriminant : PowerSeries ℚ :=
  PowerSeries.C 1 - PowerSeries.C 2 * PowerSeries.X -
    PowerSeries.C 3 * PowerSeries.X ^ 2

/-- A square root of `motzkinDiscriminant` on the branch with constant coefficient one. -/
def IsMotzkinSquareRoot (s : PowerSeries ℚ) : Prop :=
  s * s = motzkinDiscriminant ∧ PowerSeries.constantCoeff s = 1

/-- The canonical square-root branch used by the Motzkin generating functions. -/
noncomputable def motzkinSquareRoot : PowerSeries ℚ :=
  (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (motzkinDiscriminant - 1)

theorem motzkinSquareRoot_isSquareRoot : IsMotzkinSquareRoot motzkinSquareRoot := by
  let u : PowerSeries ℚ := motzkinDiscriminant - 1
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    norm_num [u, motzkinDiscriminant]
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  have hone : PowerSeries.subst u (1 : PowerSeries ℚ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hu, map_one]
  constructor
  · change (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst u *
      (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst u = motzkinDiscriminant
    rw [← PowerSeries.subst_mul hu, ← PowerSeries.binomialSeries_add]
    norm_num
    have hb1 : PowerSeries.binomialSeries ℚ (1 : ℚ) = 1 + PowerSeries.X := by
      simpa using (PowerSeries.binomialSeries_nat (R := ℚ) (A := ℚ) 1)
    rw [hb1]
    simp [PowerSeries.subst_add hu, PowerSeries.subst_X hu, hone, u]
  · change PowerSeries.constantCoeff
      ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst u) = 1
    let b := PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)
    have hb0 : PowerSeries.constantCoeff (b - 1) = 0 := by
      simp [b]
    have hsub0 : PowerSeries.constantCoeff ((b - 1).subst u) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hu0 (b - 1) hb0
    have hb : b = 1 + (b - 1) := by ring
    rw [show PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) = b from rfl, hb,
      PowerSeries.subst_add hu]
    simpa [hone] using hsub0

/-- The second component of the canonical Motzkin Riordan pair. It is the
power-series quotient `(1 - X - motzkinSquareRoot) / (2X)`, expressed by a
coefficient shift so no division by `X` is required. -/
noncomputable def motzkinH : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff (n + 1) (1 - PowerSeries.X - motzkinSquareRoot) / 2

theorem two_mul_X_mul_motzkinH :
    2 * PowerSeries.X * motzkinH = 1 - PowerSeries.X - motzkinSquareRoot := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 by
    rw [PowerSeries.C_eq_algebraMap]
    exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 2).symm, mul_assoc]
  ext n
  cases n with
  | zero =>
      simp [motzkinSquareRoot_isSquareRoot.2]
  | succ n =>
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      simp [motzkinH]
      ring

/-- The first component of the canonical Motzkin Riordan pair. -/
noncomputable def motzkinG : PowerSeries ℚ :=
  motzkinSquareRoot⁻¹

theorem motzkinG_mul_motzkinSquareRoot :
    motzkinG * motzkinSquareRoot = 1 := by
  exact PowerSeries.inv_mul_cancel _ (by
    rw [motzkinSquareRoot_isSquareRoot.2]
    norm_num)

/-- The pair of generating series defining the Motzkin Riordan array.

Writing the second identity without division by `X` keeps the characterization internal to formal
power series. The constant-coefficient condition selects the intended square-root branch. -/
def IsMotzkinRiordanPair (g h : PowerSeries ℚ) : Prop :=
  ∃ s : PowerSeries ℚ,
    IsMotzkinSquareRoot s ∧ g * s = 1 ∧
      2 * PowerSeries.X * h = 1 - PowerSeries.X - s

/-- A Motzkin Riordan pair together with its defining generating-series equations. -/
structure MotzkinRiordanPair where
  g : PowerSeries ℚ
  h : PowerSeries ℚ
  isPair : IsMotzkinRiordanPair g h

namespace MotzkinRiordanPair

/-- The `(n, k)` entry of the Motzkin triangle represented by `p`. -/
noncomputable def entry (p : MotzkinRiordanPair) (n k : ℕ) : ℚ :=
  PowerSeries.coeff n (p.g * p.h ^ k)

@[simp]
theorem entry_zero_right (p : MotzkinRiordanPair) (n : ℕ) : p.entry n 0 = p.g.coeff n := by
  simp [entry]

end MotzkinRiordanPair

/-- The canonical Riordan pair defining the Motzkin triangle. -/
noncomputable def motzkinRiordanPair : MotzkinRiordanPair where
  g := motzkinG
  h := motzkinH
  isPair := ⟨motzkinSquareRoot, motzkinSquareRoot_isSquareRoot,
    motzkinG_mul_motzkinSquareRoot, two_mul_X_mul_motzkinH⟩

/-- The canonical `(n, k)` entry of the Motzkin triangle (OEIS A094531). -/
noncomputable def motzkinTriangle (n k : ℕ) : ℚ :=
  motzkinRiordanPair.entry n k

private theorem motzkinSquareRoot_coeff_one :
    PowerSeries.coeff 1 motzkinSquareRoot = -1 := by
  have hs := congrArg (PowerSeries.coeff 1) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_one_mul, motzkinDiscriminant,
    PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2] at hs ⊢
  linarith

private theorem motzkinSquareRoot_coeff_two :
    PowerSeries.coeff 2 motzkinSquareRoot = -2 := by
  have hs := congrArg (PowerSeries.coeff 2) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one] at hs ⊢
  linarith

private theorem motzkinSquareRoot_coeff_three :
    PowerSeries.coeff 3 motzkinSquareRoot = -2 := by
  have hs := congrArg (PowerSeries.coeff 3) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two] at hs ⊢
  linarith

private theorem motzkinSquareRoot_coeff_four :
    PowerSeries.coeff 4 motzkinSquareRoot = -4 := by
  have hs := congrArg (PowerSeries.coeff 4) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two,
    motzkinSquareRoot_coeff_three] at hs ⊢
  linarith

private theorem motzkinG_coeff_zero : PowerSeries.coeff 0 motzkinG = 1 := by
  simp [motzkinG, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    motzkinSquareRoot_isSquareRoot.2]

private theorem motzkinG_coeff_one : PowerSeries.coeff 1 motzkinG = 1 := by
  have hg := congrArg (PowerSeries.coeff 1) motzkinG_mul_motzkinSquareRoot
  rw [PowerSeries.coeff_one_mul] at hg
  have hg0 : PowerSeries.constantCoeff motzkinG = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using motzkinG_coeff_zero
  norm_num [motzkinG_coeff_zero,
    hg0, motzkinSquareRoot_isSquareRoot.2, motzkinSquareRoot_coeff_one] at hg ⊢
  linarith

private theorem motzkinG_coeff_two : PowerSeries.coeff 2 motzkinG = 3 := by
  have hg := congrArg (PowerSeries.coeff 2) motzkinG_mul_motzkinSquareRoot
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two] at hg ⊢
  linarith

private theorem motzkinG_coeff_three : PowerSeries.coeff 3 motzkinG = 7 := by
  have hg := congrArg (PowerSeries.coeff 3) motzkinG_mul_motzkinSquareRoot
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinG_coeff_two, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two,
    motzkinSquareRoot_coeff_three] at hg ⊢
  linarith

private theorem motzkinH_coeff_zero : PowerSeries.coeff 0 motzkinH = 0 := by
  norm_num [motzkinH, motzkinSquareRoot_coeff_one]

private theorem motzkinH_coeff_one : PowerSeries.coeff 1 motzkinH = 1 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_two]

private theorem motzkinH_coeff_two : PowerSeries.coeff 2 motzkinH = 1 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_three]

private theorem motzkinH_coeff_three : PowerSeries.coeff 3 motzkinH = 2 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_four]

/-- The first four rows of the canonical Motzkin triangle, matching OEIS A094531. -/
theorem motzkinTriangle_initial_rows :
    [[motzkinTriangle 0 0],
      [motzkinTriangle 1 0, motzkinTriangle 1 1],
      [motzkinTriangle 2 0, motzkinTriangle 2 1, motzkinTriangle 2 2],
      [motzkinTriangle 3 0, motzkinTriangle 3 1,
        motzkinTriangle 3 2, motzkinTriangle 3 3]] =
    [[1], [1, 1], [3, 2, 1], [7, 6, 3, 1]] := by
  norm_num [motzkinTriangle, motzkinRiordanPair, MotzkinRiordanPair.entry,
    pow_succ, PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinG_coeff_two, motzkinG_coeff_three,
    motzkinH_coeff_zero, motzkinH_coeff_one, motzkinH_coeff_two,
    motzkinH_coeff_three]

end MetaMathlibExt
