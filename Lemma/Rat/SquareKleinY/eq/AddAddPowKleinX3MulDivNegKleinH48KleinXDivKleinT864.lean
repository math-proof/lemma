import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_EllipticCurve_RubinSilverbergFamily
open RubinSilverberg


/--
[RubinSilverberg_kleinY_sq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RubinSilverberg_kleinY_sq.lean)
-/
@[path]
private lemma main
  [Field K] [CharZero K]
  {u : K} :
-- imply
  kleinY u ^ 2 = kleinX u ^ 3 + (-kleinH u / 48) * kleinX u + kleinT u / 864 := by
-- proof
  unfold kleinY kleinX kleinH kleinT; ring


-- created on 2026-10-23
