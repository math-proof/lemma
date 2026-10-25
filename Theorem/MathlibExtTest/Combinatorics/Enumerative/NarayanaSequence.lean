/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/NarayanaSequence.lean -/


import Def.Combinatorics.Enumerative.NarayanaSequence
import Mathlib.Data.List.Range


namespace MetaMathlibExt

example : (List.range 7).map narayanaCowsSequence = [0, 1, 1, 1, 2, 3, 4] := by
  decide

example (n : ℕ) :
    narayanaCowsSequence (n + 3) =
      narayanaCowsSequence (n + 2) + narayanaCowsSequence n :=
  rfl

end MetaMathlibExt
