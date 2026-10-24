import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_FibrePoly
import Lemma.Int.P2MUtil

open Polynomial ModularCurve

/--
[ModularCurve_natDegree_fibrePoly](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_natDegree_fibrePoly.lean)
-/
@[path]
private lemma main
  [Field K]
  {Φ : Polynomial (Polynomial ℤ)}
  {a : K}
-- given
  (hΦ : Φ.Monic) :
-- imply
  (fibrePoly Φ a).natDegree = Φ.natDegree :=
  hΦ.natDegree_map _


-- created on 2026-10-23
