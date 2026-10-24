/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FiniteLiesOver.lean -/


import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOver
import Lemma.Nat.NumberField.Completion.FiniteLiesOver

/-!
# Tests for canonical finite-place completion maps

Generic checks exercising the algebra-map formula, continuity, and
injectivity of `adicCompletionMap`.
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

example (x : K) :
    adicCompletionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion L) x :=
  adicCompletionMap_algebraMap v w x

example : Continuous (adicCompletionMap v w) :=
  continuous_adicCompletionMap v w

example {a b : v.adicCompletion K}
    (h : adicCompletionMap v w a = adicCompletionMap v w b) : a = b :=
  adicCompletionMap_injective v w h

end IsDedekindDomain.HeightOneSpectrum
