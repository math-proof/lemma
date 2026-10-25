import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.AffineWeylBook
open Set AffineReflectionGroup AffineWeylGroup AffineWeylGroupData
open scoped InnerProductSpace


namespace AffineReflectionGroup

/--
[translation_subgroup_discrete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean)
-/
@[path]
private lemma translation_subgroup_discrete
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C : W.Alcove}
-- given
  (hC_open : IsOpen C.set)
  (hC_nonempty : C.set.Nonempty)
  (hdisjoint : ∀ w ∈ W.TranslationSubgroup, w ≠ 1 → Disjoint C.set ((w : AffineIsometryEquiv ℝ E E) '' C.set))
  (htransl : ∀ w ∈ W.TranslationSubgroup, ∀ y : E, (w : AffineIsometryEquiv ℝ E E) y = y + (w : AffineIsometryEquiv ℝ E E) 0) :
-- imply
  ∃ ε > 0, ∀ w ∈ W.TranslationSubgroup, w ≠ 1 → ‖((w : AffineIsometryEquiv ℝ E E) 0 : E)‖ ≥ ε := by
-- proof
  obtain ⟨x0, hx0⟩ := hC_nonempty
  obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hC_open x0 hx0
  refine ⟨ε, hε_pos, ?_⟩
  intro w hw hw_ne
  by_contra h_small
  push Not at h_small
  have h_wx0 : (w : AffineIsometryEquiv ℝ E E) x0 ∈ Metric.ball x0 ε := by
    rwa [Metric.mem_ball, dist_eq_norm, htransl w hw x0, add_sub_cancel_left]
  exact Set.disjoint_iff.mp (hdisjoint w hw hw_ne)
    ⟨hball h_wx0, x0, hx0, rfl⟩

end AffineReflectionGroup

namespace AffineReflectionGroup

end AffineReflectionGroup


-- created on 2026-10-23
-- updated on 2026-10-24
