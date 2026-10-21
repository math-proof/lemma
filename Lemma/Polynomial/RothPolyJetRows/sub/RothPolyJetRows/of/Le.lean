import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyJetRows_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [Field K]
  (f : Fin k → K[X])
  {s t : ℕ}
-- given
  (hst : s ≤ t) :
-- imply
  rothPolyJetRows f s ⊆ rothPolyJetRows f t := by
-- proof
  rintro v ⟨n, hn, rfl⟩
  refine ⟨n, hn.trans hst, rfl⟩


-- created on 2026-10-21
