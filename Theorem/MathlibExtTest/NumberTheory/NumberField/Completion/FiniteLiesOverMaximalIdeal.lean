/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FiniteLiesOverMaximalIdeal.lean -/


import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOverMaximalIdeal
import Lemma.Nat.NumberField.Completion.FiniteLiesOverMaximalIdeal


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

example :
    Ideal.comap (adicCompletionIntegersMap v w)
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
  comap_maximalIdeal_adicCompletionIntegersMap v w

example (x : v.adicCompletionIntegers K)
    (hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    adicCompletionIntegersMap v w x ∈
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) := by
  have h := comap_maximalIdeal_adicCompletionIntegersMap v w
  rw [← h] at hx
  exact Ideal.mem_comap.mp hx

example (x : v.adicCompletionIntegers K)
    (hx : adicCompletionIntegersMap v w x ∈
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have h := comap_maximalIdeal_adicCompletionIntegersMap v w
  rw [← h]
  exact Ideal.mem_comap.mpr hx

end IsDedekindDomain.HeightOneSpectrum
