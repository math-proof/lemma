/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean -/

import Mathlib.Data.List.Basic
import Def.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath


namespace MetaMathlibExt

/-- A multi-marked Dyck path: an ordered finite step sequence starting at
`(0,0)` whose every prefix is underdiagonal (vertical-step count at most the
`E`-step count) and whose full path ends on the diagonal (`E` count equals
total vertical-step count). Both plain `N` and marked `N*_t` steps move
vertically by one. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
structure MultiMarkedDyckPath where
  steps : List MultiMarkedStep
  underdiagonal :
    ∀ k, k ≤ steps.length →
      multiMarkedCountVert (steps.take k) ≤ multiMarkedCountE (steps.take k)
  diagonal_endpoint : multiMarkedCountE steps = multiMarkedCountVert steps

end MetaMathlibExt
