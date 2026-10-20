import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Spectrum.Prime.GroupAction
open scoped Pointwise
open PrimeSpectrum


/--
[smul_asIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Spectrum/Prime/GroupAction.lean)
-/
@[path]
private lemma smul_asIdeal_eq
  [Group G] [CommSemiring R] [MulSemiringAction G R]
  {g : G}
  {p : PrimeSpectrum R} :
-- imply
  (g • p).asIdeal = g • p.asIdeal := by
-- proof
  apply PrimeSpectrum.smul_asIdeal g p


-- created on 2026-10-20
