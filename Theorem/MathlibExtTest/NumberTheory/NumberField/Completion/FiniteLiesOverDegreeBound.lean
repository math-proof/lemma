/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FiniteLiesOverDegreeBound.lean -/


import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOverDegreeBound
import Lemma.Nat.NumberField.Completion.FiniteLiesOverDegreeBound
/-!
# Tests for the local degree bound under finite-place completion

Generic checks consuming `finrank_adicCompletion_le`: one direct API
application and one downstream `calc`/transitivity use. These tests
exercise the public inequality only and do not duplicate its proof.
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

example :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤
      Module.finrank K L :=
  finrank_adicCompletion_le v w

example {n : ℕ} (h : Module.finrank K L ≤ n) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤ n :=
  calc Module.finrank (v.adicCompletion K) (w.adicCompletion L)
      ≤ Module.finrank K L := finrank_adicCompletion_le v w
    _ ≤ n := h

end IsDedekindDomain.HeightOneSpectrum
