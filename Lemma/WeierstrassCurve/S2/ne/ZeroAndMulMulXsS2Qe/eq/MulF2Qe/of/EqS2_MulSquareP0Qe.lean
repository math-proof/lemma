import Mathlib
import sympy.Basic


@[path]
private lemma main
  [Field F]
  {x xa xb xg xs x2 Sk Sk1 Skm Fk Fk1 Fkm p1 p0 pm Qe P2e S2 F2
    b2 b4 b6 b8 : F}
-- given
  (hM0 : xa * Sk = Fk)
  (hMm : xg * Skm = Fkm)
  (hM1 : xb * Sk1 = Fk1)
  (hD1 : Fk1 * Sk - Fk * Sk1 = -p1)
  (hD1m : Fk * Skm - Fkm * Sk = -pm)
  (hD2a : Fk1 * Skm - Fkm * Sk1 = -(p0 * Qe))
  (hD3a : (x * Sk - Fk) ^ 2 = Sk1 * Skm)
  (hPsi : S2 = p0 ^ 2 * Qe)
  (hPhi : F2 = x * S2 - p1 * pm)
  (hg4 : (xs + x2) * (xb - xg) ^ 2 =
    2 * (xb * xg) * (xb + xg) + b2 * (xb * xg) + b4 * (xb + xg) + b6)
  (hdup : x2 * Qe = P2e)
  (hg3 : (xb + xg) * (xa - x) ^ 2 =
    2 * (xa * x) * (xa + x) + b2 * (xa * x) + b4 * (xa + x) + b6)
  (hg3p : xb * xg * (xa - x) ^ 2 =
    (xa * x) ^ 2 - b4 * (xa * x) - b6 * (xa + x) - b8)
  (hbrel : 4 * b8 = b2 * b6 - b4 ^ 2)
  (hQv : Qe = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
  (hP2v : P2e = x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8)
  (hQne : Qe ≠ 0)
  (hSk1ne : Sk1 ≠ 0)
  (hSkmne : Skm ≠ 0)
  (haxne : xa ≠ x)
  (hbgne : xb ≠ xg) :
-- imply
  S2 ≠ 0 ∧ xs * S2 * Qe = F2 * Qe := by
-- proof
  have hp1 : p1 = -(Sk * Sk1 * (xb - xa)) := by
    linear_combination hD1 + Sk * hM1 - Sk1 * hM0
  have hpm : pm = -(Sk * Skm * (xa - xg)) := by
    linear_combination hD1m + Skm * hM0 - Sk * hMm
  have hP0 : p0 * Qe = -(Sk1 * Skm * (xb - xg)) := by
    linear_combination hD2a + Skm * hM1 - Sk1 * hMm
  have hSpk : Sk1 * Skm = Sk ^ 2 * (x - xa) ^ 2 := by
    linear_combination -hD3a + (2 * x * Sk - Fk - xa * Sk) * hM0
  have hbig : ((xs - x) * (x - xa) ^ 2 * (xb - xg) ^ 2 + (xb - xa) * (xa - xg) * Qe) *
      (Qe * (xa - x) ^ 2) = 0 := by
    rw [hQv, hP2v] at hdup
    rw [hQv]
    linear_combination
      (b2 * x ^ 6 - 4 * b2 * x ^ 5 * xa + 6 * b2 * x ^ 4 * xa ^ 2 - 4 * b2 * x ^ 3 * xa ^ 3 +
        b2 * x ^ 2 * xa ^ 4 + 4 * x ^ 7 - 16 * x ^ 6 * xa + 24 * x ^ 5 * xa ^ 2 -
        16 * x ^ 4 * xa ^ 3 + 4 * x ^ 3 * xa ^ 4 + 2 * b4 * x ^ 5 - 8 * b4 * x ^ 4 * xa +
        12 * b4 * x ^ 3 * xa ^ 2 - 8 * b4 * x ^ 2 * xa ^ 3 + 2 * b4 * x * xa ^ 4 +
        b6 * x ^ 4 - 4 * b6 * x ^ 3 * xa + 6 * b6 * x ^ 2 * xa ^ 2 - 4 * b6 * x * xa ^ 3 +
        b6 * xa ^ 4) * hg4 +
      (-x ^ 4 * xb ^ 2 + 2 * x ^ 4 * xb * xg - x ^ 4 * xg ^ 2 + 4 * x ^ 3 * xa * xb ^ 2 -
        8 * x ^ 3 * xa * xb * xg + 4 * x ^ 3 * xa * xg ^ 2 - 6 * x ^ 2 * xa ^ 2 * xb ^ 2 +
        12 * x ^ 2 * xa ^ 2 * xb * xg - 6 * x ^ 2 * xa ^ 2 * xg ^ 2 + 4 * x * xa ^ 3 * xb ^ 2 -
        8 * x * xa ^ 3 * xb * xg + 4 * x * xa ^ 3 * xg ^ 2 - xa ^ 4 * xb ^ 2 +
        2 * xa ^ 4 * xb * xg - xa ^ 4 * xg ^ 2) * hdup +
      (b2 * x ^ 5 * xa - b2 * x ^ 5 * xb - b2 * x ^ 5 * xg - 2 * b2 * x ^ 4 * xa ^ 2 +
        2 * b2 * x ^ 4 * xa * xb + 2 * b2 * x ^ 4 * xa * xg + 2 * b2 * x ^ 4 * xb * xg -
        b2 * x ^ 3 * xa ^ 2 * xb - b2 * x ^ 3 * xa ^ 2 * xg - 4 * b2 * x ^ 3 * xa * xb * xg +
        2 * b2 * x ^ 2 * xa ^ 2 * xb * xg + 6 * x ^ 6 * xa - 5 * x ^ 6 * xb - 5 * x ^ 6 * xg -
        10 * x ^ 5 * xa ^ 2 + 10 * x ^ 5 * xa * xb + 10 * x ^ 5 * xa * xg +
        8 * x ^ 5 * xb * xg - 5 * x ^ 4 * xa ^ 2 * xb - 5 * x ^ 4 * xa ^ 2 * xg -
        16 * x ^ 4 * xa * xb * xg + 8 * x ^ 3 * xa ^ 2 * xb * xg + b2 * b4 * x ^ 2 * xa ^ 2 -
        b4 * x ^ 5 + b4 * x ^ 4 * xa - b4 * x ^ 4 * xb - b4 * x ^ 4 * xg +
        2 * b4 * x ^ 3 * xa ^ 2 + 2 * b4 * x ^ 3 * xa * xb + 2 * b4 * x ^ 3 * xa * xg +
        4 * b4 * x ^ 3 * xb * xg - b4 * x ^ 2 * xa ^ 2 * xb - b4 * x ^ 2 * xa ^ 2 * xg -
        8 * b4 * x ^ 2 * xa * xb * xg + 4 * b4 * x * xa ^ 2 * xb * xg - b2 * b6 * x ^ 3 +
        3 * b2 * b6 * x ^ 2 * xa + b4 ^ 2 * x ^ 3 - b4 ^ 2 * x ^ 2 * xa +
        2 * b4 ^ 2 * x * xa ^ 2 - 5 * b6 * x ^ 4 + 10 * b6 * x ^ 3 * xa + b6 * x ^ 3 * xb +
        b6 * x ^ 3 * xg + 2 * b6 * x ^ 2 * xa ^ 2 - 2 * b6 * x ^ 2 * xa * xb -
        2 * b6 * x ^ 2 * xa * xg + 2 * b6 * x ^ 2 * xb * xg + b6 * x * xa ^ 2 * xb +
        b6 * x * xa ^ 2 * xg - 4 * b6 * x * xa * xb * xg + 2 * b6 * xa ^ 2 * xb * xg +
        b2 * b8 * x * xa + b4 * b6 * x ^ 2 + 3 * b4 * b6 * x * xa + b4 * b6 * xa ^ 2 +
        2 * b8 * x ^ 2 * xa + b8 * x ^ 2 * xb + b8 * x ^ 2 * xg + 2 * b8 * x * xa ^ 2 -
        2 * b8 * x * xa * xb - 2 * b8 * x * xa * xg + b8 * xa ^ 2 * xb + b8 * xa ^ 2 * xg +
        b4 * b8 * x + b4 * b8 * xa + b6 ^ 2 * x + b6 ^ 2 * xa + b6 * b8) * hg3 +
      (b2 ^ 2 * x ^ 2 * xa ^ 2 - 4 * b2 * x ^ 4 * xa + 12 * b2 * x ^ 3 * xa ^ 2 + 4 * x ^ 6 -
        24 * x ^ 5 * xa + 36 * x ^ 4 * xa ^ 2 + 2 * b2 * b4 * x ^ 2 * xa +
        2 * b2 * b4 * x * xa ^ 2 - 4 * b4 * x ^ 4 + 8 * b4 * x ^ 3 * xa +
        12 * b4 * x ^ 2 * xa ^ 2 + b2 * b6 * x ^ 2 + b2 * b6 * xa ^ 2 + 4 * b4 ^ 2 * x * xa -
        4 * b6 * x ^ 3 + 12 * b6 * x ^ 2 * xa + 2 * b4 * b6 * x + 2 * b4 * b6 * xa -
        4 * b8 * x ^ 2 + 8 * b8 * x * xa - 4 * b8 * xa ^ 2 + b6 ^ 2) * hg3p +
      (b2 * x ^ 4 * xa - 2 * b2 * x ^ 3 * xa ^ 2 + b2 * x ^ 2 * xa ^ 3 - x ^ 6 +
        6 * x ^ 5 * xa - 9 * x ^ 4 * xa ^ 2 + 4 * x ^ 3 * xa ^ 3 + b4 * x ^ 4 -
        3 * b4 * x ^ 2 * xa ^ 2 + 2 * b4 * x * xa ^ 3 + 2 * b6 * x ^ 3 -
        3 * b6 * x ^ 2 * xa + b6 * xa ^ 3 + b8 * x ^ 2 - 2 * b8 * x * xa + b8 * xa ^ 2) * hbrel
  have hcoreE : (xs - x) * (x - xa) ^ 2 * (xb - xg) ^ 2 + (xb - xa) * (xa - xg) * Qe = 0 :=
    (mul_eq_zero.mp hbig).resolve_right
      (mul_ne_zero hQne (pow_ne_zero 2 (sub_ne_zero.mpr (fun hE => haxne hE))))
  have hp0ne : p0 * Qe ≠ 0 := by
    rw [hP0]
    apply neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hSk1ne hSkmne) (sub_ne_zero.mpr hbgne))
  refine ⟨?_, ?_⟩
  ·
    intro hS20
    apply hp0ne
    have h0 : p0 ^ 2 * Qe = 0 := by
      rw [← hPsi]
      apply hS20
    obtain h | h := mul_eq_zero.mp h0
    ·
      obtain h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      rw [h', zero_mul]
    · apply absurd h hQne
  · linear_combination (-Qe) * hPhi + (Qe * (xs - x)) * hPsi + (Qe * pm) * hp1 +
      (Qe * Sk * Sk1 * (xa - xb)) * hpm +
      ((xs - x) * (Qe * p0 - Sk1 * Skm * xb + Sk1 * Skm * xg)) * hP0 +
      ((xs - x) * (xb - xg) ^ 2 * (Sk ^ 2 * (xa - x) ^ 2 + Sk1 * Skm) -
        Qe * Sk ^ 2 * (xa - xb) * (xa - xg)) * hSpk +
      (Sk ^ 4 * (xa - x) ^ 2) * hcoreE


-- created on 2026-10-24
