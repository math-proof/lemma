/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FiniteLiesOverResidueField.lean -/


import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOverResidueField
import Lemma.Nat.NumberField.Completion.FiniteLiesOverResidueField
/-!
# Checks for adic integer map naturality
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

example (a : 𝓞 K) :
    (adicCompletionIntegersMap v w)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) =
      algebraMap (𝓞 L) (w.adicCompletionIntegers L)
        (algebraMap (𝓞 K) (𝓞 L) a) :=
  adicCompletionIntegersMap_algebraMap v w a

example (a : 𝓞 K) :
    ((adicCompletionIntegersMap v w)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) :
      w.adicCompletion L) =
      ((algebraMap (𝓞 L) (w.adicCompletionIntegers L)
        (algebraMap (𝓞 K) (𝓞 L) a)) :
        w.adicCompletion L) := by
  rw [adicCompletionIntegersMap_algebraMap]

example (a : 𝓞 K) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
      ((adicCompletionIntegersMap v w)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (algebraMap (𝓞 L) (w.adicCompletionIntegers L)
          (algebraMap (𝓞 K) (𝓞 L) a)) := by
  rw [adicCompletionIntegersMap_algebraMap]

end IsDedekindDomain.HeightOneSpectrum
