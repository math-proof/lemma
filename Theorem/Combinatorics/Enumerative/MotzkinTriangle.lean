/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.MotzkinTriangle
/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/


namespace MetaMathlibExt

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

end MetaMathlibExt
