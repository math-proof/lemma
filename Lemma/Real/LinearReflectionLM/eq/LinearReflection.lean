import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs
open Set FiniteReflectionGroups
open scoped InnerProductSpace


/--
[linearReflectionLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/FiniteReflectionGroups/Defs.lean)
-/
@[path]
private lemma main
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {α v : E} :
-- imply
  linearReflectionLM α v = linearReflection α v :=
-- proof
  rfl


-- created on 2026-10-23
-- updated on 2026-10-24
