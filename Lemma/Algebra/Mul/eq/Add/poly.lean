import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [CommRing α]
  {x t0 t1 t2 t3 : α} :
-- imply
  (x - t0) * (x - t1) * (x - t2) * (x - t3) =
    x⁴
      - (t0 + t1 + t2 + t3) * x³
      + (t0 * t1 + t0 * t2 + t0 * t3 + t1 * t2 + t1 * t3 + t2 * t3) * x²
      - (t0 * t1 * t2 + t0 * t1 * t3 + t0 * t2 * t3 + t1 * t2 * t3) * x
      + t0 * t1 * t2 * t3 := by
-- proof
  ring


-- created on 2018-11-15
-- updated on 2026-08-20
