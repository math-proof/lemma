import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.LocalRing.Henselian


/--
[HenselianLocalRing.of_isAdicComplete_maximalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/Henselian.lean)
-/
@[path]
private lemma HenselianLocalRing_of_isAdicComplete_maximalIdeal_eq
  [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
-- imply
  HenselianLocalRing R := by
-- proof
  apply HenselianLocalRing.of_isAdicComplete_maximalIdeal R


-- created on 2026-10-20
