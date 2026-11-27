module

public import Mathlib

public section

open scoped Pointwise


namespace AdditiveCombinatorics

/--
[plunnecke_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Plunnecke.lean)
-/
public theorem plunnecke_inequality
  [DecidableEq Z]
  [AddCommGroup Z]
  {A B : Finset Z}
  {K : NNRat}
  {m n : ℕ}
-- given
  (hA : A.Nonempty)
  (hK : ((A + B).card : NNRat) ≤ K * A.card) :
-- imply
  ((m • B - n • B).card : NNRat) ≤ K ^ (m + n) * A.card := by
-- proof
  have hAcard : (0 : NNRat) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hle : ((A + B).card : NNRat) / A.card ≤ K := by
    rwa [div_le_iff₀ hAcard]
  calc ((m • B - n • B).card : NNRat)
    ≤ ((A + B).card / A.card) ^ (m + n) * A.card :=
      Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA B m n
    _ ≤ K ^ (m + n) * A.card := by gcongr

end AdditiveCombinatorics


-- created on 2026-10-23
