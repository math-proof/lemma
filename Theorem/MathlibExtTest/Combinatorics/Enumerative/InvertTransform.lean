/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/InvertTransform.lean -/
module

public import Def.Combinatorics.Enumerative.InvertTransform
public import Theorem.Finset.Enumerative.InvertTransform
open MetaMathlibExt

public section

example (a : ℕ → ℤ) :
    (1 - PowerSeries.X * PowerSeries.mk a) *
      (1 + PowerSeries.X * PowerSeries.mk (invertTransform a)) = 1 := by
  exact invertTransform_spec a

