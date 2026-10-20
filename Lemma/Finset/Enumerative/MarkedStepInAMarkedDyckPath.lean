import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MarkedStepInAMarkedDyckPath
open MetaMathlibExt


/--
[MarkedDyckPath.size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMarkedDyckPath.lean)
-/
@[path]
private lemma MarkedDyckPath_size_eq_eq
  {P : MarkedDyckPath} :
-- imply
  P.pathSize = markedDyckCountN P.steps + 2 * markedDyckCountNstar P.steps := by
-- proof
  apply MetaMathlibExt.MarkedDyckPath.size_eq P


-- created on 2026-10-20
