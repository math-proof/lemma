import Mathlib
import sympy.Basic
import Lemma.ModularCurve.LaurentCoeff
open ModularCurve IntermediateField HahnSeries


/--
[ModularCurve_coeffMap_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_coeffMap_injective.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S]
  {f : R →+* S}
-- given
  (hf : Function.Injective f) :
-- imply
  Function.Injective (ModularCurve.coeffMap f) :=
-- proof
  fun x y hxy => by
    ext k
    exact hf (by simpa using congrArg (fun z => HahnSeries.coeff z k) hxy)


-- created on 2026-10-23
