import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Pointwise


namespace PrimeSpectrum

/--
[smul_asIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Spectrum/Prime/GroupAction.lean)
-/
@[path]
lemma smul_asIdeal
  [Group G] [CommSemiring R] [MulSemiringAction G R]
  {g : G}
  {p : PrimeSpectrum R} :
-- imply
  (g • p).asIdeal = g • p.asIdeal :=
-- proof
  rfl

end PrimeSpectrum


-- created on 2026-10-20
-- updated on 2026-10-26
