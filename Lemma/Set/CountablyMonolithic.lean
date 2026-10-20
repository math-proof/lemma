import Mathlib
import sympy.Basic
import sympy.atlas.Topology.CountablyMonolithic


/--
[hasCountableNetwork_of_secondCountable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/CountablyMonolithic.lean)
-/
@[path]
private lemma hasCountableNetwork_of_secondCountable_eq
  [TopologicalSpace X] [SecondCountableTopology X] :
-- imply
  HasCountableNetwork X := by
-- proof
  apply hasCountableNetwork_of_secondCountable X


-- created on 2026-10-20
