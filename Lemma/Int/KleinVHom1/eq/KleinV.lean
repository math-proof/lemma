import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.EllipticCurve_RubinSilverbergFamily
open RubinSilverberg


/--
[RubinSilverberg_kleinVHom_one_right](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RubinSilverberg_kleinVHom_one_right.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {n : R} :
-- imply
  kleinVHom n 1 = kleinV n := by
-- proof
  unfold kleinVHom kleinV; ring


-- created on 2026-10-23
