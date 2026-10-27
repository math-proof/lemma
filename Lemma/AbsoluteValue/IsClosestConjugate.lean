import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Normed.IsClosestConjugate

/--
[IsClosestConjugate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Field/IsClosestConjugate.lean)
-/
@[path]
private lemma lt_spectral_norm_sub_of_is_conj_root_lt
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {α β α' : AlgebraicClosure K}
-- given
  (h : AlgebraicClosure.IsClosestConjugate K α β)
  (hconj : IsConjRoot K α α')
  (hne : α ≠ α') :
-- imply
  spectralNorm K (AlgebraicClosure K) (α - β) <
    spectralNorm K (AlgebraicClosure K) (α - α') := by
-- proof
  apply AlgebraicClosure.IsClosestConjugate.lt_spectralNorm_sub_of_isConjRoot h hconj hne


/--
[IsClosestConjugate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Field/IsClosestConjugate.lean)
-/
@[path]
private lemma adjoin_le
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {α β : AlgebraicClosure K}
-- given
  (h : AlgebraicClosure.IsClosestConjugate K α β)
  (hsep : IsSeparable K α) :
-- imply
  IntermediateField.adjoin K {α} ≤ IntermediateField.adjoin K {β} := by
-- proof
  apply AlgebraicClosure.IsClosestConjugate.adjoin_le h hsep


-- created on 2026-10-10
-- updated on 2026-10-26
