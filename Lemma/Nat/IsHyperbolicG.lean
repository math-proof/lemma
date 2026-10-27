import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.GroupTheory.HyperbolicGroup
open Group Nat


namespace Definitions
end Definitions
namespace Group

/--
[IsHyperbolic.of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IsHyperbolicG.lean)
-/
@[path]
private lemma IsHyperbolic.of_subsingleton
  [Group G] [Subsingleton G] :
-- imply
  IsHyperbolic G := by
-- proof
  refine ⟨Empty, inferInstance, ⟨Empty.elim, Subsingleton.elim _ _⟩, 0, le_refl 0, fun w x y z => ?_⟩
  rw [Subsingleton.elim x w, Subsingleton.elim y w, Subsingleton.elim z w, min_self, sub_zero]

end Group

/--
[IsHyperbolic.fg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/IsHyperbolicG.lean)
-/
@[path]
private lemma IsHyperbolic.fg
  [Group G]
-- given
  (h : IsHyperbolic G) :
-- imply
  Group.FG G := by
-- proof
  obtain ⟨ι, hι, P, _, _⟩ := h
  letI := hι
  rw [Group.fg_iff]
  exact ⟨Set.range P.val, P.closure_eq_top, Set.finite_range P.val⟩


-- created on 2026-10-20
-- updated on 2026-10-26
