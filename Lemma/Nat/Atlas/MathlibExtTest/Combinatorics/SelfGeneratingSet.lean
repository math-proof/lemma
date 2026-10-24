import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Combinatorics.SelfGeneratingSet
open scoped Classical


namespace MetaMathlibExt.SelfGeneratingSet

/--
[succ_strictGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SelfGeneratingSet.lean)
-/
@[path]
Tests for the self-generating set API using seed `0` and the successor generator.
-/
private lemma succ_strictGrowth : StrictGrowth {fun n => n + 1} := by
  intro f hf x
  have hf' : f = (fun n => n + 1) := Finset.mem_singleton.mp hf
  rw [hf']
  exact Nat.lt_succ_self x

end MetaMathlibExt.SelfGeneratingSet


-- created on 2026-10-23
