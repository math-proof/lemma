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
end MetaMathlibExt
