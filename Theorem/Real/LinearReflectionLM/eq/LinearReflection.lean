module

public import Mathlib
public import Def.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs.Part4

public section

open Set FiniteReflectionGroups
open scoped InnerProductSpace


/--
[linearReflectionLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/FiniteReflectionGroups/Defs.lean)
-/
public theorem Real.LinearReflectionLM.eq.LinearReflection
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {α v : E} :
-- imply
  linearReflectionLM α v = linearReflection α v :=
-- proof
  rfl


-- created on 2026-10-23
-- updated on 2026-10-26
