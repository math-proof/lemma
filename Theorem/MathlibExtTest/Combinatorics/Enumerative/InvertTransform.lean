/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/InvertTransform.lean -/

import Def.Combinatorics.Enumerative.InvertTransform
import Theorem.Finset.Enumerative.InvertTransform
open MetaMathlibExt


example (a : ℕ → ℤ) :
    (1 - PowerSeries.X * PowerSeries.mk a) *
      (1 + PowerSeries.X * PowerSeries.mk (invertTransform a)) = 1 := by
  exact invertTransform_spec a

