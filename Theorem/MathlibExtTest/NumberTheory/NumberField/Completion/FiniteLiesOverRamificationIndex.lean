/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FiniteLiesOverRamificationIndex.lean -/

/-
Author: @toskua, Avocado
-/


import Lemma.Nat.NumberField.Completion.FiniteLiesOverRamificationIndex
/-!
# Test file
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))

variable [w.asIdeal.LiesOver v.asIdeal]

example : Function.Injective (adicCompletionIntegersMap v w) :=
  adicCompletionIntegersMap_injective v w

example :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
        (v.adicCompletionIntegers K) =
      w.asIdeal.ramificationIdx (𝓞 K) :=
  ramificationIdx_adicCompletionIntegersMap v w

example :
    ((IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
        (v.adicCompletionIntegers K) = 1) ↔
      w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  rw [ramificationIdx_adicCompletionIntegersMap v w]

end IsDedekindDomain.HeightOneSpectrum
