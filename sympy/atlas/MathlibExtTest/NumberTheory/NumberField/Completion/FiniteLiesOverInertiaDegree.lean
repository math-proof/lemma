/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FiniteLiesOverInertiaDegree.lean -/


import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverInertiaDegree
import Lemma.Nat.NumberField.Completion.FiniteLiesOverInertiaDegree

/-!
# Test file
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [w.asIdeal.LiesOver v.asIdeal]

example :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      adicCompletionIntegersMap v w := by
  ext x
  rfl

example :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).inertiaDeg
        (v.adicCompletionIntegers K) =
      w.asIdeal.inertiaDeg (𝓞 K) :=
  inertiaDeg_adicCompletionIntegersMap v w

example :
    ((IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).inertiaDeg
        (v.adicCompletionIntegers K) = 1) ↔
      w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  rw [inertiaDeg_adicCompletionIntegersMap v w]

end IsDedekindDomain.HeightOneSpectrum

-- End of file.
