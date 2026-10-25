import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.MarkedStepInAMarkedDyckPath.Part2
open MetaMathlibExt


namespace MetaMathlibExt

/--
[MarkedDyckPath.size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMarkedDyckPath.lean)
-/
@[path]
lemma MarkedDyckPath.size_eq
  {P : MarkedDyckPath} :
-- imply
  P.pathSize = markedDyckCountN P.steps + 2 * markedDyckCountNstar P.steps := by
-- proof
  unfold MarkedDyckPath.pathSize
  have h := P.balanced
  omega

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
