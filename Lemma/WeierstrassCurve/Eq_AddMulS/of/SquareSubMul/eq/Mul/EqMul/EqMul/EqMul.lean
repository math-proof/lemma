import Mathlib
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Field F]
  {x Fj Sj Fjp Sjp Fjm Sjm xj xjm xjp b2 b4 b6 : F}
-- given
  (hMj : xj * Sj = Fj)
  (hMjm : xjm * Sjm = Fjm)
  (hMjp : xjp * Sjp = Fjp)
  (hsum : (xjp + xjm) * (xj - x) ^ 2 =
    2 * (xj * x) * (xj + x) + b2 * (xj * x) + b4 * (xj + x) + b6)
  (hd3 : (x * Sj - Fj) ^ 2 = Sjp * Sjm) :
-- imply
  2 * x * Fj * (Fj + x * Sj) + b2 * x * (Fj * Sj) + b4 * ((Fj + x * Sj) * Sj) +
      b6 * Sj ^ 2 = Fjp * Sjm + Fjm * Sjp := by
-- proof
  linear_combination
    ((xjp + xjm) * (Sj * xj - 2 * x * Sj + Fj) -
      (2 * x * (Fj + xj * Sj) + 2 * x ^ 2 * Sj + b2 * x * Sj + b4 * Sj)) * hMj +
    (-Sj ^ 2) * hsum + (xjp + xjm) * hd3 + Sjm * hMjp + Sjp * hMjm


-- created on 2026-10-24
