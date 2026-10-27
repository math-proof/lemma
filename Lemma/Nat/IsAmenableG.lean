import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.GroupTheory.AmenableGroup
open scoped Pointwise Classical symmDiff


namespace Definitions
end Definitions
/--
[isAmenable_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AmenableGroup.lean)
-/
@[path]
private lemma isAmenable_of_finite
  [Group G] [Finite G] :
-- imply
  IsAmenable G := by
-- proof
  letI := Fintype.ofFinite G
  intro K ε hε
  refine ⟨Finset.univ, ⟨1, Finset.mem_univ 1⟩, fun s _ => ?_⟩
  rw [Finset.smul_finset_univ, symmDiff_self]
  simpa using hε

/--
[isAmenable_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AmenableGroup.lean)
-/
@[path]
private lemma isAmenable_of_subsingleton
  [Group G] [Subsingleton G] :
-- imply
  IsAmenable G := by
-- proof
  intro K ε hε
  refine ⟨{1}, Finset.singleton_nonempty 1, fun s _ => ?_⟩
  rw [Finset.smul_finset_singleton, Subsingleton.elim (s • (1 : G)) 1, symmDiff_self]
  simpa using hε


-- created on 2026-10-20
-- updated on 2026-10-26
