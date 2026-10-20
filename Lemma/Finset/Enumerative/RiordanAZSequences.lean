import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RiordanAZSequences
open MetaMathlibExt


/--
[riordan_iff_AZ_sequences](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanAZSequences.lean)
-/
@[path]
private lemma riordan_iff_AZ_sequences_eq
  {d : ℕ → ℕ → ℤ}
-- given
  (htri : ∀ n k : ℕ, n < k → d n k = 0) :
-- imply
  ((∃ g f : PowerSeries ℤ, PowerSeries.constantCoeff (R := by
-- proof
  apply MetaMathlibExt.riordan_iff_AZ_sequences d htri


-- created on 2026-10-20
