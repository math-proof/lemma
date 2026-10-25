import Mathlib
import sympy.Basic
import Class.Topology.CountablyMonolithic


/--
[hasCountableNetwork_of_secondCountable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/CountablyMonolithic.lean)
-/
@[path]
lemma hasCountableNetwork_of_secondCountable
  [TopologicalSpace X] [SecondCountableTopology X] :
-- imply
  HasCountableNetwork X := by
-- proof
  obtain ⟨𝒩, h𝒩_countable, _h𝒩_nonempty, h𝒩_basis⟩ :=
    TopologicalSpace.exists_countable_basis X
  refine ⟨𝒩, h𝒩_countable, ?_⟩
  intro U hU x hx
  exact h𝒩_basis.exists_subset_of_mem_open hx hU


-- created on 2026-10-20
-- updated on 2026-10-23
