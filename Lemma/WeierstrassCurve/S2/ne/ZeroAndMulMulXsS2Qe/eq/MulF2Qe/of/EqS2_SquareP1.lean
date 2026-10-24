import Mathlib
import sympy.Basic


@[path]
private lemma main
  [Field F]
  {x xa xb xg xd xs Sk Sk1 Skm Sk2 Fk Fk1 Fkm Fk2 p1 p0 p2 Qe S2 F2
    b2 b4 b6 b8 : F}
-- given
  (hM0 : xa * Sk = Fk)
  (hMm : xg * Skm = Fkm)
  (hM1 : xb * Sk1 = Fk1)
  (hM2 : xd * Sk2 = Fk2)
  (hD1 : Fk1 * Sk - Fk * Sk1 = -p1)
  (hD2a : Fk1 * Skm - Fkm * Sk1 = -(p0 * Qe))
  (hD2b : Fk2 * Sk - Fk * Sk2 = -(p2 * Qe))
  (hD3a : (x * Sk - Fk) ^ 2 = Sk1 * Skm)
  (hD3b : (x * Sk1 - Fk1) ^ 2 = Sk2 * Sk)
  (hPsi : S2 = p1 ^ 2)
  (hPhi : F2 = x * S2 - p2 * p0 * Qe)
  (hg1 : (xs + x) * (xb - xa) ^ 2 =
    2 * (xb * xa) * (xb + xa) + b2 * (xb * xa) + b4 * (xb + xa) + b6)
  (hg2 : (xd + xa) * (xb - x) ^ 2 =
    2 * (xb * x) * (xb + x) + b2 * (xb * x) + b4 * (xb + x) + b6)
  (hg3 : (xb + xg) * (xa - x) ^ 2 =
    2 * (xa * x) * (xa + x) + b2 * (xa * x) + b4 * (xa + x) + b6)
  (hg3p : xb * xg * (xa - x) ^ 2 =
    (xa * x) ^ 2 - b4 * (xa * x) - b6 * (xa + x) - b8)
  (hbrel : 4 * b8 = b2 * b6 - b4 ^ 2)
  (hQv : Qe = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
  (hSkne : Sk ≠ 0)
  (hSk1ne : Sk1 ≠ 0)
  (hbane : xb ≠ xa) :
-- imply
  S2 ≠ 0 ∧ xs * S2 * Qe = F2 * Qe := by
-- proof
  have hp1 : p1 = -(Sk * Sk1 * (xb - xa)) := by
    linear_combination hD1 + Sk * hM1 - Sk1 * hM0
  have hP0 : p0 * Qe = -(Sk1 * Skm * (xb - xg)) := by
    linear_combination hD2a + Skm * hM1 - Sk1 * hMm
  have hP2 : p2 * Qe = -(Sk * Sk2 * (xd - xa)) := by
    linear_combination hD2b + Sk * hM2 - Sk2 * hM0
  have hSpk : Sk1 * Skm = Sk ^ 2 * (x - xa) ^ 2 := by
    linear_combination -hD3a + (2 * x * Sk - Fk - xa * Sk) * hM0
  have hSpk1 : Sk2 * Sk = Sk1 ^ 2 * (x - xb) ^ 2 := by
    linear_combination -hD3b + (2 * x * Sk1 - Fk1 - xb * Sk1) * hM1
  have hcore : (xs - x) * (xb - xa) ^ 2 * Qe +
      (x - xa) ^ 2 * (x - xb) ^ 2 * (xd - xa) * (xb - xg) = 0 := by
    linear_combination Qe * hg1 + ((x - xa) ^ 2 * (xb - xg)) * hg2 +
      (-(2 * (xb * x) * (xb + x) + b2 * (xb * x) + b4 * (xb + x) + b6 -
        2 * xa * (xb - x) ^ 2) - 4 * xb * (x - xa) * (x - xb)) * hg3 +
      (4 * (x - xa) * (x - xb)) * hg3p + (-((x - xa) * (x - xb))) * hbrel +
      (2 * (xa * xb) * (xa + xb) + b2 * (xa * xb) + b4 * (xa + xb) + b6 -
        2 * x * (xa - xb) ^ 2) * hQv
  refine ⟨?_, ?_⟩
  ·
    rw [hPsi, hp1]
    apply pow_ne_zero 2 (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hSkne hSk1ne)
      (sub_ne_zero.mpr hbane)))
  · linear_combination (-Qe) * hPhi + (Qe * (xs - x)) * hPsi +
      (Qe * (xs - x) * (Sk * Sk1 * xa - Sk * Sk1 * xb + p1)) * hp1 +
      (Qe * p0) * hP2 + (Sk * Sk2 * (xa - xd)) * hP0 +
      (-(Sk * Sk2 * (xa - xd) * (xb - xg))) * hSpk +
      (-(Sk ^ 2 * (x - xa) ^ 2 * (xa - xd) * (xb - xg))) * hSpk1 +
      (Sk ^ 2 * Sk1 ^ 2) * hcore


-- created on 2026-10-24
