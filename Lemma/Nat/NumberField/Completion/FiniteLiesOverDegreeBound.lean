import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverDegreeBound
open scoped NumberField NumberField.LiesOver TensorProduct Valued
open IsDedekindDomain.HeightOneSpectrum


/--
[finrank_adicCompletion_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverDegreeBound.lean)
-/
@[path]
private lemma finrank_adicCompletion_le_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤
    Module.finrank K L := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion_le v w


-- created on 2026-10-20
