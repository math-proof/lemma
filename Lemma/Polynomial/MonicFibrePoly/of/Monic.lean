import Mathlib
import sympy.Basic
import Lemma.ModularCurve.FibrePoly
import Lemma.Int.P2MUtil

open Polynomial ModularCurve

/--
[ModularCurve_monic_fibrePoly](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_monic_fibrePoly.lean)
-/
@[path]
private lemma main
  [Field K]
  {Φ : Polynomial (Polynomial ℤ)}
  {a : K}
-- given
  (hΦ : Φ.Monic) :
-- imply
  (fibrePoly Φ a).Monic :=
  hΦ.map _


-- created on 2026-10-23
