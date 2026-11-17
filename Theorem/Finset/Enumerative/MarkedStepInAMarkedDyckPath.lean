module

public import Mathlib
public import Def.Combinatorics.Enumerative.MarkedStepInAMarkedDyckPath.Part2

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[MarkedDyckPath.size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMarkedDyckPath.lean)
-/
public theorem MarkedDyckPath.size_eq
  {P : MarkedDyckPath} :
-- imply
  P.pathSize = markedDyckCountN P.steps + 2 * markedDyckCountNstar P.steps := by
-- proof
  unfold MarkedDyckPath.pathSize
  have h := P.balanced
  omega

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
