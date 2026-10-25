/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Field/IsClosestConjugate.lean -/


import Def.Analysis.Normed.Field.IsClosestConjugate
import Lemma.AbsoluteValue.IsClosestConjugate


namespace AlgebraicClosure

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {α β α' : AlgebraicClosure K}

example (h : IsClosestConjugate K α β)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hne : σ α ≠ α) :
    spectralNorm K (AlgebraicClosure K) (β - α) <
      spectralNorm K (AlgebraicClosure K) (β - σ α) :=
  h σ hne

example (h : IsClosestConjugate K α β)
    (hconj : IsConjRoot K α α') (hne : α ≠ α') :
    spectralNorm K (AlgebraicClosure K) (α - β) <
      spectralNorm K (AlgebraicClosure K) (α - α') :=
  h.lt_spectralNorm_sub_of_isConjRoot hconj hne

example (h : IsClosestConjugate K α β) (hsep : IsSeparable K α) :
    IntermediateField.adjoin K {α} ≤ IntermediateField.adjoin K {β} :=
  h.adjoin_le hsep

end AlgebraicClosure
