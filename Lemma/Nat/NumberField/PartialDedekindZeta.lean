import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.PartialDedekindZeta
open NumberField


namespace NumberField

/--
[partialDedekindZeta_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PartialDedekindZeta.lean)
-/
@[path]
lemma partialDedekindZeta_empty
  [Field K] [NumberField K]
  {s : ℂ} :
-- imply
  partialDedekindZeta K ∅ s = 1 := by
-- proof
  simp [partialDedekindZeta]

end NumberField

namespace NumberField

/--
[partialDedekindZeta_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PartialDedekindZeta.lean)
-/
@[path]
lemma partialDedekindZeta_singleton
  [Field K] [NumberField K]
  {𝔭 : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K)}
  {s : ℂ} :
-- imply
  partialDedekindZeta K {𝔭} s =
      (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ := by
-- proof
  simp [partialDedekindZeta]

end NumberField


-- created on 2026-10-20
-- updated on 2026-10-26
