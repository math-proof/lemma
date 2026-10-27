import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Pointwise


namespace AdditiveCombinatorics

/--
[plunnecke_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Plunnecke.lean)
-/
@[path]
lemma plunnecke_inequality
  [DecidableEq Z]
  [AddCommGroup Z]
  {A B : Finset Z}
  {K : ℚ≥0}
  {m n : ℕ}
-- given
  (hA : A.Nonempty)
  (hK : ((A + B).card : ℚ≥0) ≤ K * A.card) :
-- imply
  ((m • B - n • B).card : ℚ≥0) ≤ K ^ (m + n) * A.card := by
-- proof
  have hAcard : (0 : ℚ≥0) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hle : ((A + B).card : ℚ≥0) / A.card ≤ K := by
    rwa [div_le_iff₀ hAcard]
  calc ((m • B - n • B).card : ℚ≥0)
    ≤ ((A + B).card / A.card) ^ (m + n) * A.card :=
      Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA B m n
    _ ≤ K ^ (m + n) * A.card := by gcongr

end AdditiveCombinatorics


-- created on 2026-10-23
