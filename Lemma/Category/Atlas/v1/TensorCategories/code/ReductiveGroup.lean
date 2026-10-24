import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.ReductiveGroup
open ReductiveGroupData


namespace ReductiveGroupData

/--
[u_acts_trivially_on_summand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ReductiveGroup.lean)
-/
@[path]
lemma u_acts_trivially_on_summand
  {D : ReductiveGroupData}
  {i : D.I} :
-- imply
  ∀ w : D.V, D.mem_sub (D.W i) w → ∀ u : D.U, D.act (D.u_incl u) w = w := by
-- proof
  obtain ⟨W_U, hW_U⟩ := D.fixed_pts_sub (D.W i)
  have hW_U_nonempty : ∃ w : D.V, D.mem_sub W_U w ∧ w ≠ D.v_zero := by
    obtain ⟨w, hw_mem, hw_ne, hw_fix⟩ := D.unipotent_fixed_pt (D.W i) (D.W_nonempty i)
    exact ⟨w, (hW_U w).mpr ⟨hw_mem, hw_fix⟩, hw_ne⟩
  have hW_U_sub : ∀ w : D.V, D.mem_sub W_U w → D.mem_sub (D.W i) w := by
    intro w hw
    exact ((hW_U w).mp hw).1
  have hW_sub_WU : ∀ w : D.V, D.mem_sub (D.W i) w → D.mem_sub W_U w :=
    D.irred i W_U hW_U_sub hW_U_nonempty
  intro w hw u
  exact ((hW_U w).mp (hW_sub_WU w hw)).2 u

end ReductiveGroupData

namespace ReductiveGroupData

/--
[u_acts_trivially](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ReductiveGroup.lean)
-/
@[path]
lemma u_acts_trivially
  {D : ReductiveGroupData} :
-- imply
  ∀ v : D.V, ∀ u : D.U, D.act (D.u_incl u) v = v := by
-- proof
  intro v u
  have h_fixes_summands : ∀ i : D.I, ∀ w : D.V,
    D.mem_sub (D.W i) w → D.act (D.u_incl u) w = w :=
    fun i w hw => D.u_acts_trivially_on_summand i w hw u
  exact D.completely_reducible (D.u_incl u) h_fixes_summands v

end ReductiveGroupData

namespace ReductiveGroupData

/--
[u_is_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ReductiveGroup.lean)
-/
@[path]
lemma u_is_trivial
  {D : ReductiveGroupData} :
-- imply
  ∀ u : D.U, u = D.u_one := by
-- proof
  intro u
  apply D.u_faithful
  intro v
  exact D.u_acts_trivially v u

end ReductiveGroupData

namespace ReductiveGroupData

/--
[lemma_1_30_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ReductiveGroup.lean)
-/
@[path]
lemma lemma_1_30_2
  {D : ReductiveGroupData}
  {D : ReductiveGroupData} :
-- imply
  ∀ u : D.U, u = D.u_one :=
-- proof
  D.u_is_trivial

end ReductiveGroupData


-- created on 2026-10-23
