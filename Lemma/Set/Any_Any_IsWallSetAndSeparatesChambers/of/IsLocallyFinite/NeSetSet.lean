import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Reflection.WallSeparationCorollary
open Set HyperplaneArrangement
open scoped InnerProductSpace


namespace HyperplaneArrangement

/--
[wall_of_C_separates_distinct_chambers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparationCorollary.lean)
-/
@[path]
lemma wall_of_C_separates_distinct_chambers
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C D : arr.Chamber}
-- given
  (hne : C.set ≠ D.set)
  (hlf : arr.IsLocallyFinite) :
-- imply
  ∃ η, ∃ hη : η ∈ arr.hyperplanes, η.IsWall C.set ∧ SeparatesChambers η hη C D := by
-- proof
  obtain ⟨η, _, hη, hwall, hsep⟩ := wall_separates_distinct_chambers C D hne hlf
  exact ⟨η, hη, hwall, hsep⟩

end HyperplaneArrangement


-- created on 2026-10-23
