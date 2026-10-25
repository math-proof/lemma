import Mathlib
import Lemma.DedekindDomain.IntegralClosure
section

variable (K : Type*) [Field K] [NumberField K]

open IsDedekindDomain NumberField HeightOneSpectrum

instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := Countable.of_equiv _
  Rat.HeightOneSpectrum.primesEquiv.symm

instance : Countable (HeightOneSpectrum (𝓞 K)) :=
  Set.Countable.of_preimage_singleton <| fun y ↦
  ((preimage_comap_finite (𝓞 ℚ) ℚ K (𝓞 K)) {y} (by simp)).countable
end
