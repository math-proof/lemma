/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/PartialDedekindZeta.lean -/


import Def.NumberTheory.NumberField.PartialDedekindZeta
import Lemma.Nat.NumberField.PartialDedekindZeta


namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

example (s : ℂ) : partialDedekindZeta K ∅ s = 1 := by
  simp

example (𝔭 : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K)) (s : ℂ) :
    partialDedekindZeta K {𝔭} s =
      (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ := by
  simp

end NumberField
