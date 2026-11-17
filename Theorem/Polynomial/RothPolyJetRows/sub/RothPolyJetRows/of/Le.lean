module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyJetRows_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Polynomial.RothPolyJetRows.sub.RothPolyJetRows.of.Le
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
-- updated on 2026-11-13
