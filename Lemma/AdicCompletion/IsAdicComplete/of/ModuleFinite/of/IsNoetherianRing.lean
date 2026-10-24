import Mathlib
import sympy.Basic
import Lemma.AdicCompletion.Support.IsAdicCompleteM

open AdicCompletionSupport

/--
[IsAdicComplete_of_finite_of_isNoetherianRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAdicComplete_of_finite_of_isNoetherianRing.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  {I : Ideal R} [IsAdicComplete I R] :
-- imply
  IsAdicComplete I M :=
-- proof
  isAdicComplete_of_moduleFinite_of_isNoetherianRing


-- created on 2026-10-24
